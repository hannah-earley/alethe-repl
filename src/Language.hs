module Language where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Vector (Vector,(!))
import Data.Char
import Data.Maybe (catMaybes)
import Data.List (intercalate)
import Control.Monad (liftM2)
import Control.Arrow (first)
import qualified Text.Parsec.Error as PE

import Helper

-- main interface

data Term = Atom     Integer String
          | Var      String
          | Asymm    Term Term
          | Compound [Term]
          deriving (Eq)

data Definition = Terminus [Term]
                | Rule { _defLPatt :: [Context]
                       , _defRPatt :: [Context]
                       , _defRules :: [Declaration] }

data Declaration = Declaration { _decWeight :: Int
                               , _decRule   :: Context }

data Context = Context { _cOHC  :: Term
                       , _cTerm :: [Term]}

-- display, sugar, properties, etc

instance Show Term where
    show (Atom n a)   = showAtom n a
    show (Var v)      = v
    show (Asymm l r)  = "(" ++ show l ++ " ! " ++ show r ++ ")"
    show (Compound t) = showComp t

instance Show Definition where
    show (Terminus t)         = "! " ++ showSp t ++ ";"
    show (Rule lhs rhs rules) = showRuleHead lhs rhs ++ showRules show rules

showRuleHead lhs rhs = case ruleInfixP lhs rhs of
                         Just (lhs',op,rhs') ->
                            showSp lhs' ++ " " ++ showInfix op ++ " " ++ showSp rhs'
                         Nothing -> showRuleHead' lhs rhs
showRuleHead' [Context c1@(Var ('|':_)) lp] [Context c2 rp]
    | c1 == c2 = showSp lp ++ " = " ++ showSp rp
showRuleHead' lhs rhs = showCtxts lhs ++ " = " ++ showCtxts rhs

ruleInfixP :: [Context] -> [Context] -> Maybe ([Term], Term, [Term])
ruleInfixP [Context c1@(Var ('|':_)) (op:lhs@(_:_))] [Context c2 (tt:rhs@(_:_))]
  | c1 == c2 && op == last rhs && last lhs == termTerm && tt == termTerm
              = Just (init lhs, op, init rhs)
ruleInfixP _ _ = Nothing

showInfix :: Term -> String
showInfix (Compound t) = "`" ++ showSp t ++ "`"
showInfix (Atom 0 a@(x:_)) | not (invalidAtom a) && not (reservedOpStart x) = a
showInfix (Atom n a) | not (invalidAtom a) = "~" ++ show n ++ ":" ++ a
showInfix t = "`" ++ show t ++ "`"

showCtxts [c] = show c
showCtxts cs = "{ " ++ showSemi cs ++ " }"

showRules _ [] = ";"
showRules f xs = ":" ++ concatMap (("\n    " ++) . f) xs

showAtom' a = if invalidAtom a then "#" ++ show a else a
showAtom n a | at == atomZero = "0"
             | at == atomNil  = "[]"
             where at = Atom n a
showAtom 0 a = showAtom' a
showAtom n a = "#~" ++ show n ++ ":" ++ if invalidAtom a then show a else a

showComp t = let c = Compound t in
             case catMaybes [show <$> nat' c, show <$> str' c, sexpr' c] of
               (x:_) -> x
               []    -> "(" ++ showSp t ++ ")"

instance Show Declaration where
    show (Declaration w r) = show r ++ replicate w '.'

instance Show Context where
    show (Context c p) = show c ++ "| " ++ showSp p

nonVisible       = isControl        ||| isSpace  ||| isSeparator
reservedIdLetter = nonVisible       ||| (`elem` ".:;`#|!$=~@()[]{}\"")
reservedIdStart  = reservedIdLetter ||| isDigit
reservedOpStart  = reservedIdStart  ||| isLetter ||| (`elem` "'_")

invalidAtom (x:xs) = isLower x || reservedIdStart x || any reservedIdLetter xs
invalidAtom [] = False

resolveAtomVar name@(x:_)
  | isLower x || x `elem` "_" = Var name
resolveAtomVar name           = atom name

atom = Atom 0
term0 = Compound []
termTerm = Compound []
term1 = list1 id Compound

atomZero = atom "Z"
atomSucc = atom "S"
atomNil = atom "Nil"
atomCons = atom "Cons"
atomDup = atom "Dup"
atomPlus = atom "Plus"
atomMinus = atom "Minus"
atomChar c = atom ['\'', c]

nats = iterate (\n -> Compound [atomSucc, n]) atomZero
nat = (nats!!) . fromIntegral
cons car cdr = Compound [atomCons, car, cdr]
sexpr = flip $ foldr cons
slist = foldr cons atomNil
str = slist . map atomChar

nat' (Compound [x,y]) | x == atomSucc = (1+) <$> nat' y
nat' a                | a == atomZero = Just (0 :: Integer)
nat' _                                = Nothing

str' (Compound [x, Atom 0 ['\'', c], cs]) | x == atomCons = (c:) <$> str' cs
str' a                                    | a == atomNil  = Just ""
str' _                                                    = Nothing

sexpr' t@(Compound [x, _, _]) | x == atomCons = Just $ "[" ++ intercalate " " (sexpr'' t) ++ "]"
sexpr' _                                      = Nothing
sexpr'' (Compound [x, car, cdr]) | x == atomCons = show car : sexpr'' cdr
sexpr'' a                        | a == atomNil  = []
sexpr'' e                                        = [".", show e]

-- term manipulation

termLeft :: Term -> Term
termLeft (Asymm l _) = l
termLeft (Compound t) = Compound $ map termLeft t
termLeft x = x

termRight :: Term -> Term
termRight (Asymm l _) = l
termRight (Compound t) = Compound $ map termRight t
termRight x = x

class Kappa a where
    asplit :: a -> (a,a)
    vars :: a -> Set String
    unify :: a -> a -> Maybe (Map String [Term])
    compatible :: a -> a -> Bool

    varsplit :: a -> (Set String, a, a)
    varsplit t = let (l,r) = asplit t in (vars t, l, r)

zipStrict :: [a] -> [b] -> Maybe [(a,b)]
zipStrict []     []     = Just []
zipStrict (x:xs) (y:ys) = (:) (x,y) <$> zipStrict xs ys
zipStrict _      _      = Nothing

zipWithStrict :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWithStrict f xs ys = map (uncurry f) <$> zipStrict xs ys

instance Kappa a => Kappa [a] where
    asplit = unzip . map asplit
    vars = S.unions . map vars
    unify xs ys = M.unionsWith (++) <$> (zipWithStrict unify xs ys >>= sequence)
    compatible xs ys = maybe False (all $ uncurry compatible) $ zipStrict xs ys

instance Kappa Term where
    asplit = liftM2 (,) termLeft termRight

    vars (Atom _ _)  = S.empty
    vars (Var v)     = S.singleton v
    vars (Asymm l r) = S.union (vars l) (vars r)
    vars (Compound t)= vars t

    unify a@(Atom _ _) b@(Atom _ _) = if a == b then Just M.empty else Nothing
    unify (Var v)      t            = Just (M.singleton v [t])
    unify (Compound s) (Compound t) = unify s t
    unify _            _            = Nothing

    compatible (Var _)      _             = True
    compatible _            (Var _)       = True
    compatible a@(Atom _ _) b@(Atom _ _)  = a == b
    compatible (Asymm l r)  t             = compatible l t || compatible r t
    compatible t            a@(Asymm _ _) = compatible a t
    compatible (Compound s) (Compound t)  = compatible s t
    compatible _            _             = False

instance Kappa Context where
    asplit (Context c p) = let (c1,c2) = asplit c
                               (p1,p2) = asplit p
                           in (Context c1 p1, Context c2 p2)

    vars (Context c p) = S.union (vars c) (vars p)
    unify (Context c1 p1) (Context c2 p2) = liftM2 (M.union) (unify p1 p2) (unify c1 c2)
    compatible (Context c1 p1) (Context c2 p2) = compatible c1 c2 && compatible p1 p2

-- compilation

newtype Program = Program [Strategy]

data Strategy = StratHalt [Term]
              | Strategy { _stLPatt :: [Context]
                         , _stRules :: Vector Context
                         , _stPlan  :: [Either Int Int]
                         , _stRPatt :: [Context] }

data KappaError = ParseError PE.ParseError
                | AmbiguityError [Definition]
                | ReversibilityError [Definition]

instance Show Strategy where
    show (StratHalt t) = show (Terminus t)
    show (Strategy l d p r) = showStratHead l r ++ showRules showp p
      where showp (Left  n) = "< " ++ show (d ! n) ++ "."
            showp (Right n) = "> " ++ show (d ! n) ++ "."

showStratHead l r =
    case ruleInfixP r l of
        Just _  -> "< " ++ showRuleHead r l
        Nothing -> "> " ++ showRuleHead l r

instance Show Program where
    show (Program xs) = showMany "\n" xs

instance Show KappaError where
    show (ParseError e) = "Parse error!: " ++ show e
    show (AmbiguityError d) = "Non-determinism detected between the following rules!:" ++ showErrDefs d
    show (ReversibilityError d) = "Couldn't find a reversible execution plan for the following!:" ++ showErrDefs d

stripChildren :: Definition -> Definition
stripChildren (Terminus t) = Terminus (t)
stripChildren (Rule l r _) = Rule l r []

showErrDefs :: [Definition] -> String
showErrDefs = concatMap (("\n    "++) . show . stripChildren)

-- evaluation

match :: Program -> Context -> [(Int,Strategy)]
match (Program []) _ = []
match (Program (x:xs)) c =
    let rest = map (first succ) $ match (Program xs) c
    in case x of
        StratHalt l        | compatible l (_cTerm c) -> (0,x) : rest
        Strategy [l] _ _ _ | compatible l c          -> (0,x) : rest
        _                                            ->         rest