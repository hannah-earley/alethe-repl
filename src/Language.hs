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
decl' col = dterm <|> dsing <|> dmult
  where
    dterm = symbol "|-" >> Right . Terminus <$> manyTill term semi

    dsing = context >>= \x -> case x of
                Context c lhs -> dsdot c lhs <|> dmult' [x]
                Phantom lhs -> dsinf lhs <|> dseq lhs

    dsdot c lhs = dot >> return (Left $ DeclContext c lhs)
    dseq lhs = symbol "=" >> many term >>= dseq' lhs
    dsinf lhs = do let bt = symbol "`"
                   op <- between bt bt (fudge <$> many term)
                            <|> (Atom <$> operator)
                   rhs <- many term
                   dsinf' lhs op rhs

    dmult = party >>= dmult'
    party = braces (semiSep context') <|> ((:[]) <$> context)
    dmult' lhs = symbol "=" >> party >>= ddef lhs

    dsinf' lhs op rhs = dseq' (sandwich op lhs termTerm) (sandwich termTerm rhs op)
      where sandwich l m r = [l] ++ m ++ [r]
    dseq' lhs rhs = dsed lhs rhs <|> ddef [Phantom lhs] [Phantom rhs]
    dsed lhs rhs = dot >> return (Left $ DeclRule lhs rhs)

    ddef lhs rhs = let top = Right . uncurry (Rule lhs rhs)
                   in ddef0 top <|> ddef1 top
    ddef0 top = semi >> return (top ([],[]))
    ddef1 top = colon >> top . partitionEithers <$> many (offside col >> decl)

    fudge [t] = t
    fudge ts = Compound ts

prog :: Stream s m Char => ParsecT s u m [Statement]
prog = manyTill (pimp <|> pdef) eof
  where
    pimp = reserved "import" >> Import <$> stringLiteral
    pdef = decl >>= \d -> case d of
                Left _ -> unexpected "declaration"
                Right e -> return $ Definition e