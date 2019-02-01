module Language where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Vector (Vector,(!))
import Data.Char
import Data.Maybe (catMaybes)
import Data.List (intercalate)
import Control.Monad (liftM2, foldM, guard)
import Control.Arrow (first)
import qualified Text.Parsec.Error as PE

import Miscellanea

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
showInfix (Atom 0 a) | validOp a = a
showInfix (Atom n a) | validOp a = "~" ++ show n ++ ":" ++ a
showInfix (Atom n []) = "~" ++ show n ++ ":"
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

validOp a@(x:_) = not (invalidAtom a) && not (reservedOpStart x)
validOp []      = False

resolveAtomVar name@(x:_)
  | isLower x || x `elem` "_" = Var name
resolveAtomVar name           = atom name

atom = Atom 0
term0 = Compound []
termTerm = Compound []
term1 = list1 id Compound
phony = Atom (-999999999)

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

    vars' :: a -> Map String Int
    vars :: a -> Set String
    vars = M.keysSet . vars'

    -- unify takes an extra argument that indicates whether a given subterm
    -- (that is explicitly pattern matched on) is in a legal state; this is
    -- mainly used to check whether each deconstructed term is in a halting state
    unify :: ([Term] -> Bool) -> a -> a -> Maybe (Map String Term)
    unify' :: a -> a -> Maybe (Map String Term)
    unify' = unify (const True)

    sub :: Map String Term -> a -> (Map String Term, a)

    compatible :: a -> a -> Bool

subMakeover :: Kappa a => Map String Term -> a -> Maybe (Map String Term, a)
subMakeover m x = let (m',x') = sub m x in
                  if S.null $ vars x `S.intersection` vars x'
                     then Just (m',x')
                     else Nothing

subAll :: Kappa a => Map String Term -> a -> Maybe (Map String Term, a)
subAll m x = let (m',x') = sub m x in
             if S.null $ vars x'
                then Just (m',x')
                else Nothing

varsplit :: Kappa a => a -> (Set String, a, a)
varsplit t = let (l,r) = asplit t in (vars t, l, r)

zipStrict :: [a] -> [b] -> Maybe [(a,b)]
zipStrict []     []     = Just []
zipStrict (x:xs) (y:ys) = (:) (x,y) <$> zipStrict xs ys
zipStrict _      _      = Nothing

instance Kappa a => Kappa [a] where
    asplit = unzip . map asplit

    vars' = M.unionsWith (+) . map vars'
    vars = S.unions . map vars

    unify p patts terms = zipStrict patts terms >>= foldM go M.empty
      where go m (patt,term) = unify p patt term >>= mapMergeDisjoint m

    sub m []     = (m,[])
    sub m (x:xs) = let (m',x') = sub m x
                       (m'',xs') = sub m' xs
                   in (m'',x':xs')

    compatible xs ys = maybe False (all $ uncurry compatible) $ zipStrict xs ys

instance Kappa Term where
    asplit = liftM2 (,) termLeft termRight

    vars' (Atom _ _)  = M.empty
    vars' (Var v)     = M.singleton v 1
    vars' (Asymm l r) = M.unionWith  max (vars' l) (vars' r)
    vars' (Compound t)= vars' t

    vars (Atom _ _)  = S.empty
    vars (Var v)     = S.singleton v
    vars (Asymm l r) = S.union (vars l) (vars r)
    vars (Compound t)= vars t

    unify _ a@(Atom _ _) b@(Atom _ _) = guard (a == b) $> M.empty
    unify _ (Var v)      t            = return $ M.singleton v t
    unify p (Compound s) (Compound t) = guard (p t) >> unify p s t
    unify _ _            _            = Nothing

    sub m a@(Atom _ _) = (m,a)
    sub m (Var v)      = case m M.!? v of
                           Just x  -> (M.delete v m, x)
                           Nothing -> (m, Var v)
    sub m (Asymm l r)  = let (m1,l') = sub m l
                             (m2,r') = sub m r
                         in (m1 `M.union` m2, Asymm l' r')
    sub m (Compound t) = Compound <$> sub m t

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

    vars' (Context c p)= M.unionWith (+) (vars' c) (vars' p)
    vars (Context c p) = S.union (vars c) (vars p)

    unify p (Context c1 p1) (Context c2 p2) = unify p (c1:p1) (c2:p2)

    sub m (Context c p) = let (m',c') = sub m c
                              (m'',p') = sub m' p
                          in (m'', Context c' p')

    compatible (Context c1 p1) (Context c2 p2) = compatible c1 c2 && compatible p1 p2

-- compilation

newtype Program = Program [Strategy]

data Strategy = StratHalt [Term]
              | Strategy { _stLPatt :: [Context]
                         , _stRules :: Vector Context
                         , _stPlan  :: [Either Int Int]
                         , _stRPatt :: [Context] }

data CompilationError = ParseError PE.ParseError
                | AmbiguityError [Definition]
                | ReversibilityError [Definition]
                | VarConflictError [Definition]

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

instance Show CompilationError where
    show (ParseError e) = "Parse error!: " ++ show e
    show (AmbiguityError d) = "Non-determinism detected between the following rules!:" ++ showErrDefs d
    show (ReversibilityError d) = "Couldn't find a reversible execution plan for the following!:" ++ showErrDefs d
    show (VarConflictError d) = "Conflicting variables in the following!:" ++ showErrDefs d

stripChildren :: Definition -> Definition
stripChildren (Terminus t) = Terminus (t)
stripChildren (Rule l r _) = Rule l r []

showErrDefs :: [Definition] -> String
showErrDefs = concatMap (("\n    "++) . show . stripChildren)

-- evaluation

data EvalStatus = EvalOk
                | EvalStuck
                | EvalAmbiguous
                | EvalUndefined
                | EvalMalformed
                | EvalCorrupt
                deriving (Eq,Ord,Show)

match :: Program -> [Context] -> [(Int,Strategy)]
match (Program [])     _ = []
match (Program (x:xs)) c =
    let rest = map (first succ) $ match (Program xs) c
    in case x of
        StratHalt p       | compatible [p] (map _cTerm c) -> (0,x) : rest
        Strategy  p _ _ _ | compatible  p  c              -> (0,x) : rest
        _                                                 ->         rest

isHalting :: Program -> [Term] -> Bool
isHalting (Program []) _       = False
isHalting (Program (StratHalt x : _)) c
    | compatible x c           = True
isHalting (Program (_ : xs)) c = isHalting (Program xs) c

-- the status output indicates whether or not the computation successfully completed
-- evaluate requires its input to be in a halting state (i.e. an initial
--    state) so that it can deterministically pick an execution direction
evaluate :: Program -> [Context] -> (EvalStatus, [Context])
evaluate prog entity = case match prog entity of
    []                  -> (EvalUndefined, entity)
    [(m,StratHalt _),_] -> evaluate' prog m entity
    [_,(n,StratHalt _)] -> evaluate' prog n entity
    xs | all sh xs      -> (EvalOk,        entity)
    _                   -> (EvalAmbiguous, entity)
  where sh (_, StratHalt _) = True
        sh _                = False

-- evaluate' takes a previous strategy (Int) and continues in the same direction
evaluate' :: Program -> Int -> [Context] -> (EvalStatus, [Context])
evaluate' prog prev entity = case match prog entity of
    [(m,StratHalt _)] | m == prev               -> (EvalOk,        entity)
    [(m,s1),(n,s2)]   | m == prev               -> evaluate'' prog (n,s2) entity
                      | n == prev               -> evaluate'' prog (m,s1) entity
    [(n,s)]           | n /= prev               -> evaluate'' prog (n,s)  entity
        -- ^ the entity may no longer match the previous strategy
        --   if a parenthetical term has transitioned away
    xs                | any ((==prev) . fst) xs -> (EvalAmbiguous, entity)
    []                                          -> (EvalStuck,     entity)
    _                                           -> (EvalCorrupt,   entity)

evaluate'' :: Program -> (Int,Strategy) -> [Context] -> (EvalStatus, [Context])
evaluate'' = undefined

evaluatePartial :: Program -> [Context] -> [Context]
evaluatePartial prog = snd . evaluate prog

combineEvals :: [(EvalStatus, a)] -> (EvalStatus, [a])
combineEvals = first maximum . unzip

evalMap :: (a -> b) -> (EvalStatus, a) -> (EvalStatus, b)
evalMap f (e, x) = (e, f x)

evaluateRec :: Program -> [Context] -> (EvalStatus, [Context])
evaluateRec prog = combineEvals . map goc
  where
    goc (Context c ent) = case go (Compound ent) of
                            (e, Compound ent') -> (e,           Context c ent')
                            _                  -> (EvalCorrupt, Context c ent)

    go (Compound ts) = evalMap Compound $
                       case combineEvals $ map go ts of
                         (EvalOk,ts') -> evaluateLocal prog ts'
                         (e,ts')      -> (e, ts')
    go x@(Asymm _ _) = (EvalMalformed, x)
    go x             = (EvalOk, x)

evaluateLocal :: Program -> [Term] -> (EvalStatus, [Term])
evaluateLocal prog ts =
    let c = phony "local" in
    case evaluate prog [Context c ts] of
        (e, [Context c' ts']) | c == c' -> (e,           ts')
        _                               -> (EvalCorrupt, ts)