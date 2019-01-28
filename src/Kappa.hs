{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Kappa where

import Text.Parsec
import qualified Text.Parsec.Char as C
import qualified Text.Parsec.Token as T
-- import Text.Parsec.Combinator
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


getCol = sourceColumn . statePos <$> getParserState
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
    party = braces (sepBy context' semi) <|> ((:[]) <$> context)
    single [t] = pure t
    single _   = unexpected "group party"

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
