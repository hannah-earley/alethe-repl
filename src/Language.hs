module Language where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Monad (liftM2)
import qualified Text.Parsec.Error as PE

data Term = Atom     Integer String
          | Var      String
          | Asymm    Term Term
          | Compound [Term]
          deriving (Eq,Show)

data Definition = Terminus [Term]
                | Rule { lhs   :: [Context]
                       , rhs   :: [Context]
                       , decls :: [Context] }
                deriving (Show)

data Context = Context Term [Term]
             deriving (Show)

data KappaError = ParseError PE.ParseError
                | AmbiguityError [Definition]
                -- | IrreversibilityError [Definition]
                -- ...

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

--

termLeft :: Term -> Term
termLeft (Asymm l _) = l
termLeft (Compound t) = Compound $ map termLeft t
termLeft x = x

termRight :: Term -> Term
termRight (Asymm l _) = l
termRight (Compound t) = Compound $ map termRight t
termRight x = x

termSplit :: Term -> (Term,Term)
termSplit = liftM2 (,) termLeft termRight

varsTerm :: Term -> Set String
varsTerm (Atom _ _)  = S.empty
varsTerm (Var v)     = S.singleton v
varsTerm (Asymm l r) = S.union (varsTerm l) (varsTerm r)
varsTerm (Compound t)= varsTerms t

varsTerms :: [Term] -> Set String
varsTerms = S.unions . map varsTerm

unify :: Term -> Term -> Maybe (Map String [Term])
unify a@(Atom _ _) b@(Atom _ _) = if a == b then Just M.empty else Nothing
unify (Var v)      t            = Just (M.singleton v [t])
unify (Compound s) (Compound t) = unifies s t
unify _            _            = Nothing

unifies :: [Term] -> [Term] -> Maybe (Map String [Term])
unifies []     []     = Just M.empty
unifies (x:xs) (y:ys) = liftM2 (M.unionWith (++)) (unifies xs ys) (unify x y)
unifies _      _      = Nothing

compatible :: Term -> Term -> Bool
compatible (Var _)      _             = True
compatible _            (Var _)       = True
compatible a@(Atom _ _) b@(Atom _ _)  = a == b
compatible (Asymm l r)  t             = compatible l t || compatible r t
compatible t            a@(Asymm _ _) = compatible a t
compatible (Compound s) (Compound t)  = compatibles s t
compatible _            _             = False

compatibles :: [Term] -> [Term] -> Bool
compatibles []     []     = True
compatibles (x:xs) (y:ys) = compatible x y && compatibles xs ys
compatibles _      _      = False

compatiblec :: Context -> Context -> Bool
compatiblec (Context c1 p1) (Context c2 p2) = compatible c1 c2 && compatibles p1 p2