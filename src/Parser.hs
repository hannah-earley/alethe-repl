{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LambdaCase #-}

module Parser
( Term(..)
, Definition(..)
, Declaration(..)
, Context(..)
, Statement(..)
, Program(..)
, prog
, atomZero
, atomSucc
, atomNil
, atomCons
, atomPlus
, atomMinus
) where

import Text.Parsec
import qualified Text.Parsec.Error as E
import qualified Text.Parsec.Token as T
import Data.Char
import Data.Either (partitionEithers)

import Control.Applicative ((<*), (<$))
import Control.Monad (liftM2)
import Control.Monad.State.Lazy
import Control.Exception (bracket)
import Data.Set (Set)
import qualified Data.Set as Set

import System.Posix.Files as F
import System.Posix.Types (DeviceID, FileID, Fd)
import System.Posix.IO (fdToHandle, openFd, defaultFileFlags, OpenMode(ReadOnly))
import System.IO (hGetContents, hClose)
import System.IO.Error (catchIOError, isDoesNotExistError, isPermissionError)
import System.Directory (withCurrentDirectory)
import System.FilePath.Posix (takeDirectory, normalise, (</>))

-- combinators etc

bind2 :: Monad m => m a -> m b -> (a -> b -> m c) -> m c
bind2 mx my f = do { x <- mx; y <- my; f x y }

if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

(<??>) :: ParsecT s u m a -> [String] -> ParsecT s u m a
(<??>) = labels
infix 0 <??>

hoist :: (b -> b -> c) -> (a -> b) -> (a -> b) -> a -> c
hoist f g h = \x -> g x `f` h x

hoist2 :: (c -> c -> d) -> (a -> b -> c) -> (a -> b -> c) -> a -> b -> d
hoist2 f g h = \x y -> g x y `f` h x y

hoists :: ([b] -> c) -> [a -> b] -> a -> c
hoists f gs x = f $ map ($x) gs

($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)
infixr 4 $>

(<//>) :: FilePath -> FilePath -> FilePath
path1 <//> path2 = normalise $ path1 </> path2
infixr 5 <//>

-- parsing tools

getCol :: Monad m => ParsecT s u m Column
getCol = sourceColumn . statePos <$> getParserState

offside :: Monad m => Column -> ParsecT s u m ()
offside col = getCol >>= \col' -> if col' > col
                    then return ()
                    else parserFail "indentation error"

-- lexing and tokens

lexer = T.makeTokenParser kappaStyle
kappaStyle = T.LanguageDef
               { T.commentStart = "{-"
               , T.commentEnd = "-}"
               , T.commentLine = "--"
               , T.nestedComments = True
               , T.identStart = satisfy $ not . reservedIdStart
               , T.identLetter = satisfy $ not . reservedIdLetter
               , T.reservedNames = [ "import" ]
               , T.caseSensitive = True
               , T.opStart = satisfy $ not . reservedOpStart
               , T.opLetter = T.identLetter kappaStyle
               , T.reservedOpNames = [ ":", ";", ".", "!" ] }
  where
    nonVisible c = isControl c || isSpace c || isSeparator c
    reservedIdLetter c = nonVisible c || c `elem` ".:;`#|!$~<>()[]{}\""
    reservedIdStart c = reservedIdLetter c || isDigit c
    reservedOpStart c = reservedIdStart c || isLetter c || c `elem` "'"

identifier = T.identifier lexer
reserved = T.reserved lexer
operator = T.operator lexer
stringLiteral = T.stringLiteral lexer
natural = T.natural lexer
symbol = T.symbol lexer
lexeme = T.lexeme lexer
parens = T.parens lexer
braces = T.braces lexer
brackets = T.brackets lexer
semi = T.semi lexer
colon = T.colon lexer
dot = T.dot lexer
semiSep = T.semiSep lexer

-- types and adts

data Term = Atom String
          | Scoped Int String
          | Var String
          | Asymm Term Term
          | Compound [Term]
          deriving (Show)

data Definition = Terminus [Term]
                | Rule { lhs :: [Context]
                       , rhs :: [Context]
                       , decls :: [Declaration]
                       , defs :: [Definition] 
                       }
                deriving (Show)

data Declaration = DeclContext Term [Term]
                 | DeclRule [Term] [Term]
                 deriving (Show)

data Context = Context Term [Term]
             | Phantom [Term]
             deriving (Show)

data Statement = Import String
               | Definition Definition
               deriving (Show)

newtype Program = Program [Statement]

-- common atoms and sugar

term0 = Compound []
termTerm = Compound []
atomZero = Atom "Z"
atomSucc = Atom "S"
atomNil = Atom "Nil"
atomCons = Atom "Cons"
atomPlus = Atom "Plus"
atomMinus = Atom "Minus"
atomChar c = Atom [c]

nats = iterate (\n -> Compound [atomSucc, n]) atomZero
nat = (nats!!) . fromIntegral
cons car cdr = Compound [atomCons, car, cdr]
sexpr = flip $ foldr cons
slist = foldr cons atomNil
str = slist . map atomChar

-- parsing

idRaw = lexeme $ many (T.identLetter kappaStyle)
idQual = stringLiteral <|> idRaw
opScoped = char '~' >> liftM2 Scoped (length <$> many (char '~')) idQual

op :: Stream s m Char => ParsecT s u m Term
op = opScoped <|> opComp <|> opNorm <?> "operator"
  where
    opSub = opScoped <|> opNorm <?> "operator"
    opComp = between grave grave (fudge <$> many (opSub <|> term))
    opNorm = Atom <$> operator

    grave = symbol "`"
    fudge [t] = t
    fudge ts  = Compound ts

ident :: Stream s m Char => ParsecT s u m Term
ident = idHash <|> idFree <??> ["atom", "variable"]
  where
    idHash = char '#' >> (opScoped <|> Atom <$> idQual)
    idFree = notop >> resolve <$> identifier
    resolve id@(x:_) = if' (isLower x) Var Atom id
    notop = try . option () $ operator >>= unexpected . ("operator " ++) . show

term :: Stream s m Char => ParsecT s u m Term
term = termSugar <|> ident <|> tcomp
  where
    tcomp = (<?> "compound term") . parens . option term0 $
        term >>= hoist (<|>) tasymm tcomp'
    tasymm t = symbol "!" >> Asymm t <$> term
    tcomp' t = Compound . (t:) <$>  many term

termSugar :: Stream s m Char => ParsecT s u m Term
termSugar = tdoll <|> tnat <|> tstr <|> tlist
  where
    tdoll = symbol "$" $> Asymm atomPlus atomMinus
    tnat  = nat <$> natural
    tstr  = str <$> stringLiteral
    tlist = (<?> "list") . brackets $ liftM2 sexpr (many1 term)
                                      (option atomNil $ symbol "." >> term)

decl :: Stream s m Char => ParsecT s u m (Either Declaration Definition)
decl = getCol >>= decl'
decl' col = dterm <|> dsing <|> dmult
  where
    dterm = symbol "|-" >> Right . Terminus <$> manyTill term semi

    dsing = context' >>= \case
                Context c lhs -> hoist2 (<|>) rule1 dmult1 c lhs
                Phantom   lhs -> hoist  (<|>) dsop  dsrel    lhs

    dsrel  lhs        = symbol "=" >> many term >>= dsrel' lhs
    dsrel' lhs rhs    = rule2 lhs rhs <|> def [Phantom lhs] [Phantom rhs]
    dsop   lhs        = bind2 op (many term) $ dsop' lhs
    dsop'  lhs op rhs = dsrel' (sandwich op lhs termTerm) (sandwich termTerm rhs op)

    dmult        = party >>= dmult'
    dmult1 c lhs = dmult' [Context c lhs]
    dmult'   lhs = symbol "=" >> party >>= def lhs

    rule1 c lhs     = dot $> Left (DeclContext c lhs)
    rule2   lhs rhs = dot $> Left (DeclRule lhs rhs)

    def lhs rhs = hoist (<|>) def0 def1 $ Right . uncurry (Rule lhs rhs)
    def0 top    = semi  $> top ([],[])
    def1 top    = colon >> top . partitionEithers <$> many (offside col >> decl)
    
    party    = braces (semiSep context) <|> ((:[]) <$> context')
    context  = liftM2 Context (term <* symbol "|") (many term)
    context' = try context <|> Phantom <$> many term
    sandwich l m r = [l] ++ m ++ [r]

prog :: Stream s IO Char => ParsecT s ParseState IO [Statement]
prog = concat <$> manyTill (pimp <|> pdef) eof
  where
    pimp = reserved "import" >> stringLiteral >>= subParse
    pdef = decl >>= \case
                Left  _ -> unexpected "declaration"
                Right e -> return $ [Definition e]

-- file level parsing

data ResourceID = ResourceID DeviceID FileID deriving (Eq, Ord, Show)

resID :: Fd -> IO ResourceID
resID = (liftM2 ResourceID F.deviceID F.fileID <$>) . F.getFdStatus

data ParseState = ParseState
  { scopeCounter :: Integer
  , scopeStack :: [Integer]
  , seenFiles :: Set ResourceID
  , relPath :: FilePath
  } deriving (Show)

emptyState :: ParseState
emptyState = ParseState 1 [] Set.empty ""

liftState :: Stream s m t => ParsecT s u m a -> ParsecT s u m (a,u)
liftState p = liftM2 (,) p getState

subParse :: FilePath -> ParsecT s ParseState IO [Statement]
subParse path = getState >>= join . liftIO . attempt . withResource path . fetch
  where
    dir = takeDirectory path

    cwd = withCurrentDirectory dir

    attempt m = catchIOError m (return . die . ioMsg)

    ioMsg e state = "[" ++ realPath ++ "] System error: " ++ explain e
      where
        realPath = relPath state <//> path
        explain e | isDoesNotExistError e = "File does not exist."
                  | isPermissionError e   = "File not accessible."
                  | otherwise             = show e


    withResource path m = do
        fd  <- openFd path ReadOnly Nothing defaultFileFlags
        rid <- resID fd
        bracket (fdToHandle fd) hClose (m rid)

    fetch st rid handle
      | Set.member rid seen = return $ return []
      | otherwise           = hGetContents handle >>= (restore rel <$>) . sub
      where
        seen = seenFiles st
        rel  = relPath st
        st'  = st { seenFiles = Set.insert rid seen
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

parsePrograms :: [FilePath] -> ParsecT s ParseState IO [Statement]
parsePrograms = fmap concat . mapM subParse

loadPrograms :: [FilePath] -> IO (Either ParseError [Statement])
loadPrograms paths = runParserT (parsePrograms paths) emptyState "" ""