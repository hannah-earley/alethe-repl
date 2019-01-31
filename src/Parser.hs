module Parser
( loadPrograms
, testParse
, readInput
, prelude
) where

import Text.Parsec
import qualified Text.Parsec.Error as E
import qualified Text.Parsec.Token as T
import Text.Parsec.Language (haskellStyle)
import Data.Char
import Data.Either (partitionEithers)

import Control.Applicative ((<*), (<$))
import Control.Monad (liftM2,join)
import Control.Arrow ((***))
import Control.Monad.Trans (liftIO)
import Control.Exception (bracket)
import Data.Set (Set)
import qualified Data.Set as S

import System.Posix.Files as F
import System.Posix.Types (DeviceID, FileID, Fd)
import System.Posix.IO (fdToHandle, openFd, defaultFileFlags, OpenMode(ReadOnly))
import System.IO (hGetContents, hClose, Handle)
import System.IO.Error (catchIOError, isDoesNotExistError, isPermissionError)
import System.Directory (withCurrentDirectory)
import System.FilePath.Posix (takeDirectory)

import Language
import Helper
import Miscellanea

-- lexing and tokens

lexer = T.makeTokenParser kappaStyle
kappaStyle = haskellStyle
               { T.reservedNames = [ "import", "data" ]
               , T.identStart    = nota reservedIdStart
               , T.identLetter   = nota reservedIdLetter
               , T.opStart       = nota reservedOpStart
               , T.opLetter      = T.identLetter kappaStyle }
  where nota p = satisfy $ not . p

identifier    = T.identifier    lexer
reserved      = T.reserved      lexer
operator      = T.operator      lexer
stringLiteral = T.stringLiteral lexer
natural       = T.natural       lexer
symbol        = T.symbol        lexer
lexeme        = T.lexeme        lexer
parens        = T.parens        lexer
braces        = T.braces        lexer
brackets      = T.brackets      lexer
semi          = T.semi          lexer
colon         = T.colon         lexer
dot           = T.dot           lexer
semiSep       = T.semiSep       lexer

-- parsing tools and internal types

type Parser m a = ParsecT String ParseState m a

data ParseState = ParseState
  { scopeCounter :: Integer
  , scopeStack :: [Integer]
  , phantCtxtStack :: [Term]
  , seenFiles :: Set ResourceID
  , relPath :: FilePath }

data ResourceID = ResourceID DeviceID FileID
    deriving (Eq,Ord)

emptyState :: ParseState
emptyState = ParseState 1 [] phantoms S.empty ""

liftState :: Monad m => ParsecT s u m a -> ParsecT s u m (a,u)
liftState p = liftM2 (,) p getState

resID :: Fd -> IO ResourceID
resID = (liftM2 ResourceID F.deviceID F.fileID <$>) . F.getFdStatus

getCol :: Monad m => ParsecT s u m Column
getCol = sourceColumn . statePos <$> getParserState

offside :: Monad m => Column -> ParsecT s u m ()
offside col = getCol >>= \col' -> if col' > col
                    then return ()
                    else parserFail "indentation error"

scopeId :: Monad m => Int -> Parser m Integer
scopeId lvl = scopeStack <$> getState >>= go lvl
  where go n (l:ls) | n > 0     = go (n-1) ls
                    | n == 0    = return l
        go _ _ = unexpected "inaccessible scope"

scopePop :: Monad m => Parser m Integer
scopePop = do st <- getState
              let (x:xs) = scopeStack st
              putState $ st {scopeStack = xs}
              return x

scopePush :: Monad m => Parser m Integer
scopePush = do st <- getState
               let x = scopeCounter st
                   xs = scopeStack st
               putState $ st { scopeCounter = x+1
                             , scopeStack = x:xs}
               return x

withScope :: Monad m => Parser m x -> Parser m x
withScope a = scopePush >> liftM2 const a scopePop

phantoms :: [Term]
phantoms = map (Var . ('|':)) $ kleene ['a'..'z']

localCtxt :: Monad m => Parser m ([Term] -> Context)
localCtxt = do st <- getState
               let (c:cs) = phantCtxtStack st
               putState $ st {phantCtxtStack = cs}
               return $ Context c

kleene :: [a] -> [[a]]
kleene alpha = [reverse (x:xs) | xs <- [] : kleene alpha, x <- alpha]

-- parsing

idRaw = lexeme $ many (T.identLetter kappaStyle)
idQual = stringLiteral <|> idRaw
opScoped = liftM2 Atom sid idQual
  where sid = try $ length <$> many1 (char '~') >>= scopeId
opScoped0= liftM2 Atom sid0 idQual
  where sid0= try $ char '@' >> scopeId 0

oper :: Monad m => Parser m Term
oper = opScoped <|> opComp <|> opNorm <?> "operator"
  where
    opSub = opScoped <|> opNorm <?> "operator"
    opComp = between grave grave (term1 <$> many (opSub <|> term))
    opNorm = atom <$> operator
    grave = symbol "`"

ident :: Monad m => Parser m Term
ident = opScoped0 <|> idHash <|> idFree `labels` ["atom", "variable"]
  where
    idHash = char '#' >> (opScoped <|> atom <$> idQual)
    idFree = notop >> resolveAtomVar <$> identifier
    notop = try . option () $ operator >>= unexpected . ("operator " ++) . show

term :: Monad m => Parser m Term
term = termSugar <|> ident <|> tcomp
  where
    tcomp = (<?> "compound term") . parens . option term0 $
        term >>= liftM2 (<|>) tasymm tcomp'
    tasymm t = symbol "!" >> Asymm t <$> term
    tcomp' t = Compound . (t:) <$>  terms

terms :: Monad m => Parser m [Term]
terms = many term

termSugar :: Monad m => Parser m Term
termSugar = tdoll <|> tnat <|> tstr <|> tlist
  where
    tdoll = symbol "$" $> Asymm atomPlus atomMinus
    tnat  = nat <$> natural
    tstr  = str <$> stringLiteral
    tlist = (<?> "list") . brackets $ liftM2 sexpr terms
                                      (option atomNil $ symbol "." >> term)

decl :: Monad m => Parser m (Either [Declaration] [Definition])
decl = getCol >>= withScope . decl'
decl' col = dterm <|> dmult <|> dsing
  where
    dterm = symbol "!" >> Right . pure . Terminus <$> manyTill term semi
    dmult = join $ def    <$> party <*> dotrel
    dsing = join $ dsing' <$> terms <*> relop <*> terms

    dsing' lhs Nothing   rhs = localCtxt >>= liftM2 (<|>) f g
      where f c = dots >>= def [c lhs, c rhs] . Left
            g c =          def [c lhs]         (Right [c rhs])

    dsing' lhs (Just op) rhs = halts <$> dsing' lhs' Nothing rhs'
      where lhs' = [op] ++ lhs ++ [termTerm]
            rhs' = [termTerm] ++ rhs ++ [op]
            halts' (Compound op') = [op']
            halts' _              = []
            halts = fmap $ (++) (Terminus <$> halts' op ++ [lhs', rhs'])

    def lhs (Left w)    = return . Left $ map (Declaration w) lhs
    def lhs (Right rhs) = Right <$> liftM2 (<|>) def0 def1 (Rule lhs rhs)
    def0 top = semi  $> [top []]
    def1 top = colon >> uncurry ((:) . top) <$> subDecls col
    
    dots    = length <$> many1 dot
    dotrel  = (Left <$> dots)          <|> (symbol "=" >> Right <$> party)
    relop   = (Nothing <$ symbol "=")  <|> (Just <$> oper)
    party   = braces (semiSep context) <|> pure <$> try context
    context = liftM2 Context (option term0 term <* symbol "|") terms

subDecls :: Monad m => Column -> Parser m ([Declaration], [Definition])
subDecls col = (join *** join) . partitionEithers <$> many (offside col >> decl) 

defn :: Monad m => Parser m [Definition]
defn = decl >>= either (const $ unexpected "declaration") return

rule :: Monad m => Parser m [Declaration]
rule = decl >>= either return (const $ unexpected "definition")

imprt :: Parser IO [Definition]
imprt = reserved "import" >> stringLiteral >>= subParse

datum :: Monad m => Parser m [Definition]
datum = reserved "data" >> datum' <$> (terms <* semi)
datum' t = halts ++ [mkDef . concat $ zipWith go ps (S.toList $ vars t)]
  where (p0:ps) = phantoms
        go p v = [ Declaration 1 (Context p [opv, termTerm])
                 , Declaration 1 (Context p [termTerm, Var v, opv]) ]
          where opv = Compound [atomDup, Var v]
        t' = term1 t
        halts = Terminus <$> [t, [atomDup, t']]
        opt = Compound [atomDup, t']
        mkDef = Rule [Context p0 [opt, termTerm]] [Context p0 [termTerm, t', opt]]

prog :: Parser IO [Definition]
prog = concat <$> manyTill (imprt <|> datum <|> defn) eof

progSafe :: Monad m => Parser m [Definition]
progSafe = concat <$> manyTill (datum <|> defn) eof

-- file level parsing

withResource :: FilePath -> (ResourceID -> Handle -> IO b) -> IO b
withResource path m = do
    fd  <- openFd path ReadOnly Nothing defaultFileFlags
    rid <- resID fd
    bracket (fdToHandle fd) hClose (m rid)

subParse :: FilePath -> Parser IO [Definition]
subParse path = getState >>= join . liftIO . attempt . withResource path . fetch
  where
    dir = takeDirectory path
    cwd = withCurrentDirectory dir
    attempt m = catchIOError m (return . die . ioMsg path)

    fetch st rid handle
      | S.member rid seen = return $ return []
      | otherwise           = hGetContents handle >>= (restore rel <$>) . sub
      where
        seen = seenFiles st
        rel  = relPath st
        st'  = st { seenFiles = S.insert rid seen
                  , relPath = rel <//> dir }
        sub  = cwd . runParserT (liftState prog) st' (rel <//> path)

    restore _   (Left  e)        = bubble e
    restore rel (Right (x, st')) = putState st'' >> return x
      where st'' = st' { relPath = rel }

bubble :: Monad m => ParseError -> ParsecT s u m a
bubble = mkPT . const . return . Consumed . return . Error

die :: Monad m => (u -> String) -> ParsecT s u m a
die f = do msg <- E.Message . f <$> getState
           getPosition >>= bubble . E.newErrorMessage msg

ioMsg :: FilePath -> IOError -> ParseState -> String
ioMsg path e state = "[" ++ realPath ++ "] System error: " ++ explain
  where
    realPath = relPath state <//> path
    explain | isDoesNotExistError e = "File does not exist."
            | isPermissionError e   = "File not accessible."
            | otherwise             = show e

parsePrograms :: [FilePath] -> Parser IO [Definition]
parsePrograms = fmap concat . mapM subParse

loadPrograms :: [FilePath] -> IO (Either KappaError [Definition])
loadPrograms paths = liftErr <$> runParserT (parsePrograms paths) emptyState "" ""

liftErr :: Either ParseError a -> Either KappaError a
liftErr (Left e) = Left $ ParseError e
liftErr (Right v)= Right v

testParse :: String -> IO (Either ParseError [Definition])
testParse = runParserT prog emptyState "<local>"

readInput :: String -> Either KappaError [Declaration]
readInput = liftErr . runParser (rule <* eof) emptyState "<local>"

prelude :: [Definition]
prelude = forceEither . runParser progSafe prelState "<prelude>" $
    "data ();\n\
    \data Z;\n\
    \data S x;\n\
    \data Nil;\n\
    \data Cons car cdr;\n\
    \data Plus;\n\
    \data Minus;"
  where prelState = emptyState { scopeCounter = -1000000 }