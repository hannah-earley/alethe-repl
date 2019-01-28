{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Kappa where

import Text.Parsec
import qualified Text.Parsec.Char as C
import qualified Text.Parsec.Token as T
-- import Text.Parsec.Combinator
import Data.Char

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
reservedOp = T.reservedOp lexer
charLiteral = T.charLiteral lexer
stringLiteral = T.stringLiteral lexer
natural = T.natural lexer
-- integer = T.integer lexer
-- float = T.float lexer
-- naturalOrFloat = T.naturalOrFloat lexer
-- decimal = T.decimal lexer
-- hexadecimal = T.hexadecimal lexer
-- octal = T.octal lexer
symbol = T.symbol lexer
lexeme = T.lexeme lexer
whiteSpace = T.whiteSpace lexer
parens = T.parens lexer
braces = T.braces lexer
-- angles = T.angles lexer
brackets = T.brackets lexer
-- squares = T.squares lexer
semi = T.semi lexer
comma = T.comma lexer
colon = T.colon lexer
dot = T.dot lexer
semiSep = T.semiSep lexer
semiSep1 = T.semiSep1 lexer
commaSep = T.commaSep lexer
commaSep1 = T.commaSep1 lexer





data Term = Atom String | Var String | Asymm Term Term | Compound [Term]
    deriving (Show)

atomZero = Atom "Z"
atomSucc = Atom "S"
atomNil = Atom "Nil"
atomCons = Atom "Cons"
atomPlus = Atom "Plus"
atomMinus = Atom "Minus"
asymmDollar = Asymm atomPlus atomMinus
nat n | n < 0 = error "Natural must be non-negative"
      | n == 0 = atomZero
      | otherwise = Compound [ atomSucc, nat (n-1) ]
cons car cdr = Compound [atomCons, car, cdr]
atomChar c = Atom [c]

term = choice [ sugar <?> "literal"
              , goId <$> identifier <?> "identifier"
              , parens goParen <?> "compound term"
              ]
  where
    goId name@(x:_)
        | isLower x = Var name
        | otherwise = Atom name
    goParen = option (Compound []) $ term >>= goParen'
    goParen' x = choice [ symbol "!" >> Asymm x <$> term
                        , Compound . (x:) <$> many term ]
    goAsymm = (<?> "Asymmetry") $ do
        lhs <- term
        symbol "!"
        rhs <- term
        return $ Asymm lhs rhs
    goComp = Compound <$> many term <?> "Compound Term"

sugar = choice [ const asymmDollar <$> symbol "$"
               , Atom <$> (char '#' >> (stringLiteral <|> identifier))
               , nat <$> natural
               , goStr <$> stringLiteral
               , brackets $ option atomNil goCar
               ]
  where
    goStr [] = atomNil
    goStr (c:cs) = cons (atomChar c) (goStr cs)
    goList = goCar <|> goCdr
    goCar = do { car <- term; cdr <- goList;
                 return $ cons car cdr }
    goCdr = option atomNil $ symbol "." >> term

data Definition = Terminus [Term]
                | Rule [Context] ([Definition],[Context]) [Context]
                deriving (Show)
data Context = Context Term [Term]
                deriving (Show)

defLeft = choice [ symbol "|-" >> Terminus <$> manyTill term semi
                 , do { l <- braces (sepBy ctxt semi); symbol "="; defRight l }
                 , undefined
                 ]
defRight lhs = undefined
ctxt = do { c <- sugar; t <- many term; return $ Context c t }