module Parser where

import Text.Parsec
import qualified Text.Parsec.Error as E
import qualified Text.Parsec.Token as T
import Text.Parsec.Language (haskellStyle)
import Data.Either (partitionEithers)
import Data.Tuple (swap)

import Control.Applicative ((<*), (<$))
import Control.Monad (liftM2,liftM3,ap,join)
import Control.Monad.Trans (liftIO)
import Control.Exception (bracket)
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import System.Posix.Files as F
import System.Posix.Types (DeviceID, FileID, Fd)
import System.Posix.IO (fdToHandle, openFd, defaultFileFlags, OpenMode(ReadOnly))
import System.IO (hGetContents, hClose, Handle)
import System.IO.Error (catchIOError, isDoesNotExistError, isPermissionError)
import System.Directory (withCurrentDirectory)
import System.FilePath.Posix (takeDirectory)

import Language
import Miscellanea

-- lexing and tokens

lexer = T.makeTokenParser kappaStyle
kappaStyle = haskellStyle
               { T.reservedNames   = [ "import", "data", "_", "=" ]
               , T.reservedOpNames = [ "=" ]
               , T.identStart      = nota reservedIdStart
               , T.identLetter     = nota reservedIdLetter
               , T.opStart         = nota reservedOpStart
               , T.opLetter        = T.identLetter kappaStyle }
  where nota p = satisfy $ not . p

identifier    = T.identifier    lexer
reserved      = T.reserved      lexer
operator      = T.operator      lexer
stringLiteral = T.stringLiteral lexer
natural       = T.natural       lexer
symbol        = T.symbol        lexer
lexeme        = T.lexeme        lexer
whiteSpace    = T.whiteSpace    lexer
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
notop = try . option () $ operator >>= unexpected . ("operator " ++) . show
opScoped = liftM2 Atom sid idQual
sid = try $ length <$> many1 (char '~') >>= scopeId
opScoped' = try $ liftM2 Atom sid (notop >> identifier)
opScoped0= liftM2 Atom sid0 idQual
  where sid0= try $ char '@' >> scopeId 0

opSub :: Monad m => Parser m Term
opSub = opScoped <|> opNorm <?> "operator"
opNorm = atom <$> operator

oper :: Monad m => Parser m Term
oper = opScoped <|> opComp <|> opNorm <?> "operator"
  where
    opComp = between grave grave (term1 <$> opterms)
    grave = symbol "`"

ident :: Monad m => Parser m Term
ident = opScoped0 <|> opScoped' <|> idHash <|> idFree `labels` ["atom", "variable"]
  where
    idHash = char '#' >> (opScoped <|> atom <$> idQual)
    idFree = notop >> resolveAtomVar <$> identifier

term :: Monad m => Parser m Term
term = termSugar <|> ident <|> tcomp
  where
    tcomp = (<?> "compound term") . parens . option term0 $
        opterm >>= liftM2 (<|>) tasymm tcomp'
    tasymm t = symbol "!" >> Asymm t <$> opterm
    tcomp' t = Compound . (t:) <$> opterms

opterm :: Monad m => Parser m Term
opterm = opSub <|> termSugar <|> ident <|> tcomp
  where
    tcomp = (<?> "compound term") . parens . option term0 $
        opterm >>= liftM2 (<|>) tasymm tcomp'
    tasymm t = symbol "!" >> Asymm t <$> opterm
    tcomp' t = Compound . (t:) <$> opterms

terms :: Monad m => Parser m [Term]
terms = many term

opterms :: Monad m => Parser m [Term]
opterms = many opterm

termSugar :: Monad m => Parser m Term
termSugar = tterm <|> tdoll <|> tnat <|> tstr <|> tlist
  where
    tterm = try (reserved "_") $> termTerm
    tdoll = symbol "$" $> Asymm atomPlus atomMinus
    tnat  = nat <$> natural
    tstr  = str <$> stringLiteral
    tlist = (<?> "list") . brackets $ liftM2 sexpr opterms
                                      (option atomNil $ symbol "." >> opterm)

decl :: Monad m => Parser m [Either Declaration Definition]
decl = getCol >>= withScope . decl'
decl' col = dterm <|> dmult <|> dsing
  where
    dterm = symbol "!" >> terms >>= liftM2 (<|>) dterm' dterm''
    dmult = join $ def       <$> party <*> dotrel
    dsing = join $ dsing' [] <$> terms <*> relop <*> terms

    dterm'  t   = semi $> [Right $ Terminus t]
    dterm'' lhs = fmap go . join $ dsing' [] lhs <$> relop <*> terms'
      where
        terms' = terms <* lookAhead dot
        go (x@(Left d) : xs) = x : Right (Terminus . _cTerm $ _decRule d) : go xs
        go (x          : xs) = x : go xs
        go []                = []

    dsing' halts lhs Nothing   rhs = localCtxt >>= liftM2 (<|>) f g
      where f c = dots      >>= def [c lhs, c rhs] . Left
            g c = (halts++) <$> def [c lhs]         (Right [c rhs])

    dsing' _     lhs (Just op) rhs = dsing' halts lhs' Nothing rhs'
      where lhs' = [op] ++ lhs ++ [termTerm]
            rhs' = [termTerm] ++ rhs ++ [op]
            halts' (Compound op') = [op']
            halts' _              = []
            halts = Right . Terminus <$> halts' op ++ [lhs', rhs']

    def lhs (Left w)    = return $ map (Left . Declaration w) lhs
    def lhs (Right rhs) = (fmap Right) <$> liftM2 (<|>) def0 def1 (Rule lhs rhs)
    def0 top = semi  $> [top []]
    def1 top = colon >> uncurry ((:) . top) <$> subDecls col
    
    dots    = length <$> many1 dot
    dotrel  = (Left <$> dots)          <|> (reserved "=" >> Right <$> party)
    party   = braces (semiSep context) <|> pure <$> try context
    context = liftM2 Context (option term0 term <* symbol "|") terms

relop :: Monad m => Parser m (Maybe Term)
relop = (Nothing <$ reserved "=") <|> (Just <$> oper)

subDecls :: Monad m => Column -> Parser m ([Declaration], [Definition])
subDecls col = partitionEithers . join <$> many (offside col >> decl) 

defn :: Monad m => Parser m [Definition]
defn = decl >>= either (const $ unexpected "declaration") return . sequence

imprt :: Parser IO [Definition]
imprt = reserved "import" >> stringLiteral >>= subParse

datum :: Monad m => Parser m [Definition]
datum = reserved "data" >> datum' <$> (opterms <* semi)
datum' t = halts ++ [mkDef . concat $ zipWith go ps vs]
  where (p0:p1:ps,qs) = split phantoms
        vs = S.toList $ vars t
        v's = M.fromList $ zip vs qs
        go p v = [ Declaration 1 (Context p [opv, termTerm])
                 , Declaration 1 (Context p [termTerm, v's M.! v, opv]) ]
          where opv = Compound [atomDup, Var v]
        t' = term1 t
        Just (_, t'') = subAll v's t'
        halts = Terminus <$> [t, [atomDup, t'], [opt, termTerm], [termTerm, p1, opt]]
        opt = Compound [atomDup, t']
        mkDef = Rule [Context p0 [opt, termTerm]] [Context p0 [termTerm, t'', opt]]

prog :: Parser IO [Definition]
prog = whiteSpace >> concat <$> manyTill (imprt <|> datum <|> defn) eof

progSafe :: Monad m => Parser m [Definition]
progSafe = whiteSpace >> concat <$> manyTill (datum <|> defn) eof

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
      | otherwise         = hGetContents handle >>= (restore rel <$>) . go
      where
        seen = seenFiles st
        rel  = relPath st
        st'  = st { seenFiles = S.insert rid seen
                  , relPath = rel <//> dir }
        go   = cwd . runParserT (liftState prog) st' (rel <//> path)

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

loadPrograms :: [FilePath] -> IO (Either CompilationError [Definition])
loadPrograms paths = liftErr <$> runParserT (parsePrograms paths) emptyState "" ""

liftErr :: Either ParseError a -> Either CompilationError a
liftErr (Left e) = Left $ ParseError e
liftErr (Right v)= Right v

testParse :: Parser IO x -> String -> IO (Either ParseError x)
testParse p = runParserT p emptyState "<local>"
testLoad = testParse prog

prelude :: [Definition]
prelude = forceEither $ runParser progSafe prelState "<prelude>" prelude'
  where prelState = emptyState { scopeCounter = -1000000 }

-- user input

data Request = EvaluateOpen   [Term]
             | EvaluateClosed [Term] [Term]
             | Load           [FilePath]
             | Reload
             | Quit
             | Noop
             | ShowVars
             | ShowProg
             deriving (Show)

rule :: Monad m => Parser m Request
rule = (EvaluateOpen <$> ruleOpen) <|> (uncurry EvaluateClosed <$> ruleClosed)
  where
    ruleOpen = symbol "|" >> opterms <?> "open rule"
    ruleClosed = direction `ap` liftM3 combine terms relop terms <?> "closed rule"
    direction = (symbol ">" $> id) <|> (symbol "<" $> swap)

    combine lhs Nothing   rhs = ( lhs, rhs )
    combine lhs (Just op) rhs = ( [op] ++ lhs ++ [termTerm]
                                , [termTerm] ++ rhs ++ [op] )

cmd :: Monad m => Parser m Request
cmd = char ':' >> (quit <|> reload <|> load <|> showv <|> showp)
  where
    quit = Quit <$ symbol "q" <?> "quit (:q)"
    reload = Reload <$ symbol "r" <?> "reload (:r)"
    load = symbol "l" >> Load <$> many file <?> "load (:l file1 ...)"
    showv = ShowVars <$ symbol "v" <?> "list variables (:v)"
    showp = ShowProg <$ symbol "p" <?> "show program (:p)"
    file = stringLiteral <|> lexeme (many1 . satisfy $ not . nonVisible)


readInput :: String -> Either CompilationError Request
readInput = liftErr . runParser inp emptyState "<local>"
  where inp = whiteSpace >> option Noop (cmd <|> rule) <* eof