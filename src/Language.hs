{-# LANGUAGE NoMonomorphismRestriction #-}

module Language where

data Term = Atom     Integer String
          | Var      String
          | Asymm    Term Term
          | Compound [Term]
          deriving (Show)

data Definition = Terminus [Term]
                | Rule { lhs   :: [Context]
                       , rhs   :: [Context]
                       , decls :: [Context] }
                deriving (Show)

data Context = Context Term [Term]
             deriving (Show)

term0 = Compound []
termTerm = Compound []
atom = Atom 0
phony = Atom (-1) ""
atomZero = atom "Z"
atomSucc = atom "S"
atomNil = atom "Nil"
atomCons = atom "Cons"
atomPlus = atom "Plus"
atomMinus = atom "Minus"
atomChar c = atom [c]

nats = iterate (\n -> Compound [atomSucc, n]) atomZero
nat = (nats!!) . fromIntegral
cons car cdr = Compound [atomCons, car, cdr]
sexpr = flip $ foldr cons
slist = foldr cons atomNil
str = slist . map atomChar