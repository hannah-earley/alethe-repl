{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE LambdaCase #-}

module Language
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
import qualified Text.Parsec.Token as T
import Data.Char
import Data.Either (partitionEithers)

-- combinators etc

import Control.Applicative ((<*), (<$))
import Control.Monad (liftM2)
import Data.Function (on)

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
               , T.opStart = satisfy $ not . rservedOpStart
               , T.opLetter = T.identLetter kappaStyle
               , T.reservedOpNames = [ ":", ";", ".", "!" ] }
  where
    nonVisible c = isControl c || isSpace c || isSeparator c
    reservedIdLetter c = nonVisible c || c `elem` ".:;`#|!$@<>()[]{}\""
    reservedIdStart c = reservedIdLetter c || isDigit c
    rservedOpStart c = reservedIdStart c || isLetter c || c `elem` "'"

identifier = T.identifier lexer
reserved = T.reserved lexer
operator = T.operator lexer
stringLiteral = T.stringLiteral lexer
natural = T.natural lexer
symbol = T.symbol lexer
parens = T.parens lexer
braces = T.braces lexer
brackets = T.brackets lexer
semi = T.semi lexer
colon = T.colon lexer
dot = T.dot lexer
semiSep = T.semiSep lexer

-- token edge cases

grave = symbol "`"
notop = try . option () $ operator >>= unexpected . ("operator " ++) . show
ident = notop >> identifier <?> "identifier"

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
cons car cdr = Compound [atomCons, car, cdr]
sexpr = flip $ foldr cons
slist = foldr cons atomNil

-- parsing

term :: Stream s m Char => ParsecT s u m Term
term = termSugar <|> tid <|> tcomp
  where
    tid = resolve <$> ident <??> ["atom", "variable"]
    resolve id@(x:_) = if' (isLower x) Var Atom id
    tcomp = try tasymm <|> Compound <$> many term <?> "compound term"
    tasymm = liftM2 Asymm term (symbol "!" >> term)

termSugar :: Stream s m Char => ParsecT s u m Term
termSugar = tdoll <|> tatom' <|> tscope <|> tnat <|> tstr <|> tlist
  where
    tdoll = symbol "$" $> Asymm atomPlus atomMinus

    tatom'= char '#' >> Atom <$> (stringLiteral <|> identifier)

    tscope= liftM2 Scoped (length <$> many1 (char '@'))
                           (stringLiteral <|> identifier)

    tnat  = (nats!!) . fromInteger <$> natural

    tstr  = slist . map atomChar <$> stringLiteral

    tlist = brackets (option atomNil tlist1) <?> "list"
    tlist1= liftM2 sexpr (many1 term) (option atomNil $ symbol "." >> term)

getCol :: Monad m => ParsecT s u m Column
getCol = sourceColumn . statePos <$> getParserState

offside :: Monad m => Column -> ParsecT s u m ()
offside col = do col' <- getCol
                 if col' > col
                    then return ()
                    else parserFail "indentation error"

decl :: Stream s m Char => ParsecT s u m (Either Declaration Definition)
decl = getCol >>= decl'
decl' col = dterm <|> dsing <|> dmult
  where
    dterm = symbol "|-" >> Right . Terminus <$> manyTill term semi

    dsing = context' >>= \case
                Context c lhs -> hoist2 (<|>) rule1 dmult1 c lhs
                Phantom lhs   -> hoist  (<|>) dsop  dsrel    lhs

    dsrel  lhs        = symbol "=" >> many term >>= dsrel' lhs
    dsrel' lhs rhs    = rule2 lhs rhs <|> def [Phantom lhs] [Phantom rhs]
    dsop   lhs        = bind2 oper (many term) $ dsop' lhs
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
    oper     = between grave grave (fudge <$> many term) <|> (Atom <$> operator)

    fudge [t] = t
    fudge ts  = Compound ts
    sandwich l m r = [l] ++ m ++ [r]

prog :: Stream s m Char => ParsecT s u m [Statement]
prog = manyTill (pimp <|> pdef) eof
  where
    pimp = reserved "import" >> Import <$> stringLiteral
    pdef = decl >>= \d -> case d of
                Left _ -> unexpected "declaration"
                Right e -> return $ Definition e