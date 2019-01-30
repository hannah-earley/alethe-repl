module Parser ( loadPrograms ) where

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
import System.FilePath.Posix (takeDirectory, normalise, (</>))

import Language

-- combinators etc

if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)
infixr 4 $>

(<//>) :: FilePath -> FilePath -> FilePath
path1 <//> path2 = normalise $ path1 </> path2
infixr 5 <//>

(|||) :: Monad m => m Bool -> m Bool -> m Bool
(|||) = liftM2 (||)
infixr 2 |||

-- lexing and tokens

lexer = T.makeTokenParser kappaStyle
kappaStyle = haskellStyle
               { T.reservedNames = [ "import" ]
               , T.identStart    = nota reservedIdStart
               , T.identLetter   = nota reservedIdLetter
               , T.opStart       = nota reservedOpStart
               , T.opLetter      = T.identLetter kappaStyle }
  where
    nonVisible       = isControl        ||| isSpace  ||| isSeparator
    reservedIdLetter = nonVisible       ||| (`elem` ".:;`#|!$=~@()[]{}\"")
    reservedOpStart  = reservedIdStart  ||| isLetter
    reservedIdStart  = reservedIdLetter ||| isDigit
    nota p = satisfy $ not . p

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

type Parser a = ParsecT String ParseState IO a

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

scopeId :: Integral a => a -> Parser Integer
scopeId lvl = scopeStack <$> getState >>= go lvl
  where go n (l:ls) | n > 0     = go (n-1) ls
                    | n == 0    = return l
        go _ _ = unexpected "inaccessible scope"

scopePop :: Parser Integer
scopePop = do st <- getState
              let (x:xs) = scopeStack st
              putState $ st {scopeStack = xs}
              return x

scopePush :: Parser Integer
scopePush = do st <- getState
               let x = scopeCounter st
                   xs = scopeStack st
               putState $ st { scopeCounter = x+1
                             , scopeStack = x:xs}
               return x

withScope :: Parser x -> Parser x
withScope a = scopePush >> liftM2 const a scopePop

phantoms :: [Term]
phantoms = map (Var . ('|':)) $ kleene ['a'..'z']

localCtxt :: Parser ([Term] -> Context)
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

op :: Parser Term
op = opScoped <|> opComp <|> opNorm <?> "operator"
  where
    opSub = opScoped <|> opNorm <?> "operator"
    opComp = between grave grave (fudge <$> many (opSub <|> term))
    opNorm = atom <$> operator

    grave = symbol "`"
    fudge [t] = t
    fudge ts  = Compound ts

ident :: Parser Term
ident = opScoped0 <|> idHash <|> idFree `labels` ["atom", "variable"]
  where
    idHash = char '#' >> (opScoped <|> atom <$> idQual)
    idFree = notop >> resolve <$> identifier
    resolve id@(x:_) = if' (isLower x) Var atom id
    notop = try . option () $ operator >>= unexpected . ("operator " ++) . show

term :: Parser Term
term = termSugar <|> ident <|> tcomp
  where
    tcomp = (<?> "compound term") . parens . option term0 $
        term >>= liftM2 (<|>) tasymm tcomp'
    tasymm t = symbol "!" >> Asymm t <$> term
    tcomp' t = Compound . (t:) <$>  terms

terms :: Parser [Term]
terms = many term

terms1 :: Parser [Term]
terms1 = many1 term

termSugar :: Parser Term
termSugar = tdoll <|> tnat <|> tstr <|> tlist
  where
    tdoll = symbol "$" $> Asymm atomPlus atomMinus
    tnat  = nat <$> natural
    tstr  = str <$> stringLiteral
    tlist = (<?> "list") . brackets $ liftM2 sexpr terms1
                                      (option atomNil $ symbol "." >> term)

decl :: Parser (Either [Context] [Definition])
decl = getCol >>= withScope . decl'
decl' col = dterm <|> dmult <|> dsing
  where
    dterm = symbol "!" >> Right . pure . Terminus <$> manyTill term semi
    dmult = join $ def    <$> party <*> dotrel
    dsing = join $ dsing' <$> terms <*> relop <*> terms

    dsing' lhs Nothing   rhs = localCtxt >>= liftM2 (<|>) f g
      where f c = dot >> def [c lhs, c rhs] Nothing
            g c =        def [c lhs]       (Just [c rhs])

    dsing' lhs (Just op) rhs = terms <$> dsing' lhs' Nothing rhs'
      where lhs' = [op] ++ lhs ++ [termTerm]
            rhs' = [termTerm] ++ rhs ++ [op]
            terms= fmap ([Terminus lhs', Terminus rhs'] ++)

    def lhs Nothing    = return (Left lhs)
    def lhs (Just rhs) = Right <$> liftM2 (<|>) def0 def1 (Rule lhs rhs)
    def0 top = semi  $> [top []]
    def1 top = colon >> uncurry ((:) . top) <$> subDecls col
    
    dotrel  = (Nothing <$ dot)         <|> (symbol "=" >> Just <$> party)
    relop   = (Nothing <$ symbol "=")  <|> (Just <$> op)
    party   = braces (semiSep context) <|> pure <$> try context
    context = liftM2 Context (option term0 term <* symbol "|") terms

subDecls :: Column -> Parser ([Context], [Definition])
subDecls col = (join *** join) . partitionEithers <$> many (offside col >> decl) 

prog :: Parser [Definition]
prog = concat <$> manyTill (pimp <|> pdef) eof
  where
    pimp = reserved "import" >> stringLiteral >>= subParse
    pdef = decl >>= either (const $ unexpected "declaration") return

-- file level parsing

withResource :: FilePath -> (ResourceID -> Handle -> IO b) -> IO b
withResource path m = do
    fd  <- openFd path ReadOnly Nothing defaultFileFlags
    rid <- resID fd
    bracket (fdToHandle fd) hClose (m rid)

subParse :: FilePath -> Parser [Definition]
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
ioMsg path e state = "[" ++ realPath ++ "] System error: " ++ explain e
  where
    realPath = relPath state <//> path
    explain e | isDoesNotExistError e = "File does not exist."
              | isPermissionError e   = "File not accessible."
              | otherwise             = show e

parsePrograms :: [FilePath] -> Parser [Definition]
parsePrograms = fmap concat . mapM subParse

loadPrograms :: [FilePath] -> IO (Either KappaError [Definition])
loadPrograms paths = liftErr <$> runParserT (parsePrograms paths) emptyState "" ""
  where liftErr (Left e) = Left $ ParseError e
        liftErr (Right v)= Right v

test :: String -> IO (Either ParseError [Definition])
test = runParserT prog emptyState "<local>"