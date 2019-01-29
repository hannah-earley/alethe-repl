{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

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

term :: Stream s m Char => ParsecT s u m Term
term = termSugar <|> tid <|> tcomp
  where
    tid   = do id@(x:_) <- notop >> identifier
               return $ if isLower x then Var id else Atom id
            <?> "identifier"

    notop = try . option () $ do
                c <- try operator
                unexpected ("operator " ++ show c)

    tcomp = parens (option (Compound []) tcomp1) <?> "compound term"

    tcomp1= term >>= \t -> tasymm t <|> tcomp' t

    tasymm t = symbol "!" >> Asymm t <$> term

    tcomp' t = Compound . (t:) <$> many term

termSugar :: Stream s m Char => ParsecT s u m Term
termSugar = tdoll <|> tatom' <|> tscope <|> tnat <|> tstr <|> tlist
  where
    tdoll = symbol "$" >> return (Asymm atomPlus atomMinus)

    tatom'= char '#' >> Atom <$> (stringLiteral <|> identifier)

    tscope= do lvl <- length <$> many1 (char '@')
               Scoped lvl <$> (stringLiteral <|> identifier)

    tnat  = (nats!!) . fromInteger <$> natural

    tstr  = foldr (cons . atomChar) atomNil <$> stringLiteral

    tlist = brackets (option atomNil tlist1) <?> "list"

    tlist1= do cars <- many1 term
               cdr <- option atomNil $ symbol "." >> term
               return $ foldr cons cdr cars

context :: Stream s m Char => ParsecT s u m Context
context = option (Phantom []) $ do
            t <- term
            choice [ symbol "|" >> Context t <$> many term
                   , Phantom . (t:) <$> many term ]

context' :: Stream s m Char => ParsecT s u m Context
context' = do { c <- term; symbol "|"; Context c <$> many term }

getCol :: Monad m => ParsecT s u m Column
getCol = sourceColumn . statePos <$> getParserState

offside :: Monad m => Column -> ParsecT s u m ()
offside col = do col' <- getCol
                 if col' > col
                    then return ()
                    else parserFail "indentation error"

decl :: Stream s m Char => ParsecT s u m (Either Declaration Definition)
decl = getCol >>= decl'

decl' :: Stream s m Char => Column -> ParsecT s u m (Either Declaration Definition)
decl' col = choice
    [ symbol "|-" >> Right . Terminus <$> manyTill term semi
    , context >>= goSingle
    , party >>= goMulti
    ]
  where
    party = braces (semiSep context') <|> ((:[]) <$> context)
    infOp = between bt bt (fudge <$> many term) <|> (Atom <$> operator)
    bt = symbol "`"
    fudge [t] = t
    fudge ts = Compound ts

    goSingle (Context c lhs) = choice
        [ dot >> (pure . Left $ DeclContext c lhs)
        , goMulti [Context c lhs] ]
    goSingle (Phantom lhs) = choice
        [ do { op <- infOp; rhs <- many term; goIn lhs op rhs }
        , symbol "=" >> many term >>= goEq lhs ]
    goMulti lhs = symbol "=" >> party >>= goDef lhs

    goEq lhs rhs = choice [ dot >> (pure . Left $ DeclRule lhs rhs)
                          , goDef [Phantom lhs] [Phantom rhs] ]
    goIn lhs op rhs = goEq ([op] ++ lhs ++ [termTerm]) ([termTerm] ++ rhs ++ [op])
    goDef lhs rhs = choice [ semi >> (pure . Right $ Rule lhs rhs [] [])
                           , colon >> Right . uncurry (Rule lhs rhs) <$> goDecl ]
    goDecl = partitionEithers <$> many (offside col >> decl)

def :: Stream s m Char => ParsecT s u m Definition
def = decl >>= either (const $ unexpected "declaration") return

prog :: Stream s m Char => ParsecT s u m [Statement]
prog = manyTill (choice [ reserved "import" >> Import <$> stringLiteral 
                        , Definition <$> def ]) eof