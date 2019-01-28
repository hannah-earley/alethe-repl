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

identNotOp = try (do c <- try operator
                     unexpected ("operator " ++ show c)
                  <|> return ()
                 ) >> identifier





data Term = Atom String
          | Var String
          | Asymm Term Term
          | Compound [Term]
          deriving (Show)

data Definition = Terminus [Term]
                | Rule { lhs :: [Context]
                       , rhs :: [Context]
                       , rules :: [Context]
                       , defs :: [Definition] 
                       }
                deriving (Show)

data Context = Context Term [Term]
             | Phantom [Term]
             deriving (Show)

termTerm = Compound []
atomZero = Atom "Z"
atomSucc = Atom "S"
atomNil = Atom "Nil"
atomCons = Atom "Cons"
atomPlus = Atom "Plus"
atomMinus = Atom "Minus"
asymmDollar = Asymm atomPlus atomMinus
nat n = if n <= 0 then atomZero else Compound [ atomSucc, nat (n-1) ]
cons car cdr = Compound [atomCons, car, cdr]
atomChar c = Atom [c]

term :: Stream s m Char => ParsecT s u m Term
term = choice [ symbol "$" >> pure asymmDollar
              , char '#' >> Atom <$> (stringLiteral <|> identifier)
              , natural >>= pure . nat
              , stringLiteral >>= pure . goStr
              , brackets (option atomNil goCar) <?> "list"
              -- ^sugar
              , identNotOp >>= pure . goId <?> "identifier"
              , parens goComp <?> "compound term"
              ]
  where
    goStr [] = atomNil
    goStr (c:cs) = cons (atomChar c) (goStr cs)
    goList = goCar <|> goCdr
    goCar = do { car <- term; cdr <- goList;
                 return $ cons car cdr }
    goCdr = option atomNil $ symbol "." >> term
    goId name@(x:_) = if isLower x then Var name else Atom name
    goComp = option (Compound []) $ term >>= goComp'
    goComp' x = choice [ symbol "!" >> Asymm x <$> term
                        , Compound . (x:) <$> many term ]

context :: Stream s m Char => ParsecT s u m Context
context = option (Phantom []) $ do
            t <- term
            choice [ symbol "|" >> Context t <$> many term
                   , Phantom . (t:) <$> many term ]

context' :: Stream s m Char => ParsecT s u m Context
context' = do { c <- term; symbol "|"; Context c <$> many term }

def :: Stream s m Char => ParsecT s u m Definition
def = choice [ symbol "|-" >> Terminus <$> manyTill term semi
             , party >>= eqDef
             , context >>= \lhs -> case lhs of
                    Context c p -> eqDef [lhs]
                    Phantom t -> choice
                        [ try (symbol "-|") >> semi >> pure (Terminus t)
                        , eqDef [lhs]
                        , inDef t
                        ]
             ]
  where party = braces (sepBy context' semi)
        party' = party <|> ((:[]) <$> context)
        eqDef lhs = symbol "=" >> party' >>= go lhs
        inDef lhs = do
            op <- inOp
            rhs <- many term
            go [Phantom$ [op] ++ lhs ++ [termTerm]]
               [Phantom$ [termTerm] ++ rhs ++ [op]]
        inOp = choice [ between bt bt (fudge <$> many term)
                      , Atom <$> operator ]
        fudge [t] = t
        fudge ts = Compound ts
        go lhs rhs = choice [ semi >> pure (Rule lhs rhs [] [])
                            , colon >> uncurry (Rule lhs rhs) <$> subRules ]
        bt = symbol "`"

subRules :: Stream s m Char => ParsecT s u m ([Context],[Definition])
subRules = undefined