{-# LANGUAGE TupleSections, GeneralizedNewtypeDeriving #-}
module CP.Syntax where

import Control.Monad
import Control.Monad.Error
import Control.Monad.State
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

data Prop = Univ String Prop
          | Exist String Prop
          | Mu String Prop
          | Nu String Prop
          | OfCourse Prop
          | WhyNot Prop
          | Times Prop Prop
          | Par Prop Prop
          | One
          | Bottom
          | Plus [(String, Prop)]
          | With [(String, Prop)]
          | Var String [Prop]
          | Neg String
          | FOUniv FOType Prop
          | FOExist FOType Prop
          | Dual Prop
    deriving (Eq, Show)

type Behavior = [(String, Prop)]

--------------------------------------------------------------------------------
-- Dualizing types
dual :: Prop -> Prop
dual (Dual p)      = p
-- Variables
dual (Var s [])    = Neg s
dual (Neg s)       = Var s []
-- Multiplicative combinators
dual (a `Times` b) = dual a `Par` dual b
dual (a `Par` b)   = dual a `Times` dual b
dual One           = Bottom
dual Bottom        = One
-- Additive combinators
dual (Plus lts)    = With [(l, dual t) | (l, t) <- lts]
dual (With lts)    = Plus [(l, dual t) | (l, t) <- lts]
-- Fixed-point combinators
dual (Mu x a)      = Nu x (dual (inst x (Neg x) a))
dual (Nu x a)      = Mu x (dual (inst x (Neg x) a))
-- Exponentials
dual (OfCourse a)  = WhyNot (dual a)
dual (WhyNot a)    = OfCourse (dual a)
-- Quantifiers
dual (Univ x a)    = Exist x (dual a)
dual (Exist x a)   = Univ x (dual a)
dual (FOUniv t a)  = FOExist t (dual a)
dual (FOExist t a) = FOUniv t (dual a)

--------------------------------------------------------------------------------
-- Free propositional variables
fpv :: Prop -> [String]
-- Variables
fpv (Var s []) = [s]
fpv (Neg s)    = [s]
-- Multiplicative combinators
fpv (a `Times` b) = concatMap fpv [a,b]
fpv (a `Par` b) = concatMap fpv [a,b]
fpv One = []
fpv Bottom = []
-- Additive combinators
fpv (Plus ls) = concatMap (fpv . snd) ls
fpv (With ls) = concatMap (fpv . snd) ls
-- Fixed-point combinators
fpv (Mu x a) = filter (x /=) (fpv a)
fpv (Nu x a) = filter (x /=) (fpv a)
-- Exponentials
fpv (OfCourse a) = fpv a
fpv (WhyNot a) = fpv a
-- Quantifiers
fpv (Univ x a) = filter (x /=) (fpv a)
fpv (Exist x a) = filter (x /=) (fpv a)
fpv (FOUniv x a) = fpv a
fpv (FOExist x a) = fpv a

--------------------------------------------------------------------------------
-- Instantiating type variables
--------------------------------------------------------------------------------

class HasTyVars t
    where inst :: String -> Prop -> t -> t

instBinder x c b x' a
    | x == x' = b x a
    | otherwise = b x' (inst x c a)

instance HasTyVars Prop
    where -- Variables
          inst x c (Var x' []) | x == x' = c
                               | otherwise = Var x' []
          inst x c (Neg x') | x == x' = dual c
                            | otherwise = Neg x'
          -- Multiplicative combinators
          inst x c (a `Times` b) = inst x c a `Times` inst x c b
          inst x c (a `Par` b) = inst x c a `Par` inst x c b
          inst _ _ One = One
          inst _ _ Bottom = Bottom
          -- Additive combinators
          inst x c (Plus lts) = Plus [(l, inst x c t) | (l, t) <- lts]
          inst x c (With lts) = With [(l, inst x c t) | (l, t) <- lts]
          -- Fixed-point combinators
          inst x c (Mu x' a) = instBinder x c Mu x' a
          inst x c (Nu x' a) = instBinder x c Nu x' a
          -- Exponentials
          inst x c (OfCourse a) = OfCourse (inst x c a)
          inst x c (WhyNot a) = WhyNot (inst x c a)
          -- Quantifiers
          inst x c (Univ x' a) = instBinder x c Univ x' a
          inst x c (Exist x' a) = instBinder x c Exist x' a
          inst x c (FOUniv t a) = FOUniv t (inst x c a)
          inst x c (FOExist t a) = FOExist t (inst x c a)

data Param = ProcParam String | NameParam String
    deriving (Eq, Show)

data Arg   = ProcArg Proc | NameArg String
    deriving (Eq, Show)

data Proc = ProcVar String [Arg]
          | Link String String
          | Cut String Prop Proc Proc
          | Out String String Proc Proc
          | In String String Proc
          | Select String String Proc
          | Case String [(String, Proc)]
          | Unroll String Proc
          | Roll String String Prop Proc Proc
          | Replicate String String Proc
          | Derelict String String Proc
          | SendProp String Prop Proc
          | ReceiveProp String String Proc
          | SendTerm String FOTerm Proc
          | ReceiveTerm String String Proc
          | EmptyOut String
          | EmptyIn String Proc
          | EmptyCase String [String]
          | Quote FOTerm (Maybe Defns)
          | Unk [String]
    deriving (Eq, Show)

-- Instantiate some type variable whenever it appears in a term---used in
-- ReceiveProp.

instance HasTyVars Proc
    where inst x b = go
              where go (Link y z) = Link y z
                    go (Cut z a p q) = Cut z (inst x b a) (go p) (go q)
                    go (Out z y p q) = Out z y (go p) (go q)
                    go (In z y p) = In z y (go p)
                    go (Select x l p) = Select x l (go p)
                    go (Case z bs) = Case z [(l,) (go p) | (l, p) <- bs]
                    go (Unroll z p) = Unroll z (go p)
                    go (Roll z w a p q) = Roll z w (inst x b a) (go p) (go q)
                    go (Replicate z y p) = Replicate z y (go p)
                    go (Derelict z y p) = Derelict z y (go p)
                    go (SendProp z a p) = SendProp z (inst x b a) (go p)
                    go (ReceiveProp z x' p)
                        | x == x' = ReceiveProp z x' p
                        | otherwise = ReceiveProp z x' (go p)
                    go (EmptyOut z) = EmptyOut z
                    go (EmptyIn z p) = EmptyIn z (go p)
                    go (EmptyCase z ys) = EmptyCase z ys
                    go (Unk ys) = Unk ys

data Defn = ProcDef String [Param] Proc
          | PropDef String [String] Prop
    deriving (Eq, Show)

data Defns = D { procs :: [(String, ([Param], Proc))],
                 names :: [(String, String)],
                 types :: [(String, ([String], Prop))] }
    deriving (Eq, Show)

emptyDefns = D [] [] []


getBinding :: String -> [(String, v)] -> Either String v
getBinding k ds = case lookup k ds of
                    Nothing -> Left ("Unable to find definition of " ++ k ++ "; defined symbols are " ++ intercalate ", " (map fst ds))
                    Just v  -> Right v

getBinding' k ds = case getBinding k ds of
                     Left err -> throwError err
                     Right v  -> return v

addDefn :: Defns -> Defn -> Defns
addDefn ds (ProcDef id vs p) = ds{ procs = (id, (vs, p)) : procs ds }
addDefn ds (PropDef id vs t) = ds{ types = (id, (vs, t)) : types ds }

addNameBinding :: Defns -> String -> String -> Defns
addNameBinding ds x y = ds{ names = (x, y) : map (second exn) (names ds) }
    where exn z | z == x = y
                | otherwise = z
          second f (x, y) = (x, f y)

filterTypeDefns :: (String -> Bool) -> Defns -> Defns
filterTypeDefns p ds = ds{ types = filter (p . fst) (types ds) }

filterNameBindings :: (String -> Bool) -> Defns -> Defns
filterNameBindings p ds = ds{ names = filter (p . fst) (names ds) }

data Assertion = Assert Proc [(String, Prop)] Bool
    deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Free name and their manipulations
--------------------------------------------------------------------------------

-- Alpha-conversion (and errors, because we usually need them too) monad
newtype M t = M { unM :: StateT Int (Either String) t }
    deriving (Functor, Monad, MonadPlus, MonadState Int, MonadError String)

runM = flip evalStateT 0 . unM

fresh s = do z <- get
             put (z + 1)
             return (takeWhile ('\'' /=) s ++ '\'' : show z)


-- The free names in a process expression
fn :: Proc -> [String]
fn (Link x w)          = [x,w]
fn (Cut x _ p q)       = filter (x /=) (concatMap fn [p,q])
fn (Out x y p q)       = x : filter (y /=) (fn p) ++ fn q
fn (In x y p)          = x : filter (y /=) (fn p)
fn (Select x l p)      = x : fn p
fn (Case x bs)         = x : concatMap (fn . snd) bs
fn (Unroll x p)        = x : fn p
fn (Roll x y a p q)    = x : filter (y /=) (fn p ++ fn q)
fn (Replicate x y p)   = x : filter (y /=) (fn p)
fn (Derelict x y p)    = x : filter (y /=) (fn p)
fn (SendProp x a p)    = x : fn p
fn (ReceiveProp x a p) = x : fn p
fn (SendTerm x m p)    = x : fn p
fn (ReceiveTerm x i p) = x : fn p
fn (EmptyOut x)        = [x]
fn (EmptyIn x p)       = x : fn p
fn (EmptyCase x ys)    = x : ys
fn Quote{}             = []
fn (Unk ys)            = ys

-- 'fln p' returns the free names in 'p' that are not subject to implicit
-- weakening---i.e., the free names that are not used at types '?A'.  The name
-- was originally chosen to abbreviated "free linear names", but this is a
-- misnomer: types besides ?A can behave classically, even in the absense of
-- recursion.
fln :: Proc -> [String]
fln (Link x w)          = [x,w]
fln (Cut x _ p q)       = filter (x /=) (concatMap fln [p,q])
fln (Out x y p q)       = x : filter (y /=) (fln p) ++ fln q
fln (In x y p)          = x : filter (y /=) (fln p)
fln (Select x l p)      = x : fln p
fln (Case x bs)         = x : concatMap (fln . snd) bs
fln (Unroll x p)        = x : fn p
fln (Roll x y a p q)    = x : filter (y /=) (fn p ++ fn q)
fln (Replicate x y p)   = x : filter (y /=) (fln p)
fln (Derelict x y p)    = filter (y /=) (fln p)
fln (SendProp x a p)    = x : fln p
fln (ReceiveProp x a p) = x : fln p
fln (SendTerm x m p)    = x : fln p
fln (ReceiveTerm x i p) = x : fln p
fln (EmptyOut x)        = [x]
fln (EmptyIn x p)       = x : fln p
fln (EmptyCase x ys)    = x : ys
fln Quote{}             = []
fln (Unk ys)            = ys

-- Replace one name by another, avoiding variable capture.
replace :: String -> String -> Proc -> M Proc
replace x y = replace'
    where var z
              | x == z = y
              | otherwise = z

          replace' (ProcVar z args) = ProcVar (var z) `fmap` mapM replaceArg args
              where replaceArg (ProcArg p) = ProcArg `fmap` replace' p
                    replaceArg (NameArg s) = return (NameArg (var s))
          replace' (Link z z') = return (Link (var z) (var z'))
          replace' (Cut z a p q)
              | x == z || y == z =
                  do z' <- fresh z
                     p' <- replace z z' p
                     q' <- replace z z' q
                     liftM2 (Cut z' a) (replace' p') (replace' q')
              | otherwise = liftM2 (Cut z a) (replace' p) (replace' q)
          replace' (Out z w p q)
              | x == w || y == w =
                  do w' <- fresh w
                     p' <- replace w w' p
                     liftM2 (Out (var z) w') (replace' p') (replace' q)
              | otherwise = liftM2 (Out (var z) w) (replace' p) (replace' q)
          replace' (In z w p)
              | x == w || y == w =
                  do w' <- fresh w
                     p' <- replace w w' p
                     liftM (In (var z) w') (replace' p')
              | otherwise = liftM (In (var z) w) (replace' p)
          replace' (Select z l p) = liftM (Select (var z) l) (replace' p)
          replace' (Case z bs) = liftM (Case (var z)) (sequence [liftM (l,) (replace' p) | (l, p) <- bs])
          replace' (Unroll z p) = liftM (Unroll (var z)) (replace' p)
          replace' (Roll z w a p q)
              | x == w || y == z =
                  do w' <- fresh w
                     p' <- replace w w' p
                     q' <- replace w w' q
                     liftM2 (Roll (var z) w' a) (replace' p') (replace' q')
              | otherwise = liftM2 (Roll (var z) w a) (replace' p) (replace' q)
          replace' (Replicate z w p)
              | x == w || y == w =
                  do w' <- fresh w
                     p' <- replace w w' p
                     liftM (Replicate (var z) w') (replace' p')
              | otherwise = liftM (Replicate (var z) w) (replace' p)
          replace' (Derelict z w p)
              | x == w || y == w =
                  do w' <- fresh w
                     p' <- replace w w' p
                     liftM (Derelict (var z) w') (replace' p')
              | otherwise = liftM (Derelict (var z) w) (replace' p)
          replace' (SendProp z a p) = liftM (SendProp (var z) a) (replace' p)
          replace' (ReceiveProp z a p) = liftM (ReceiveProp (var z) a) (replace' p)
          replace' (SendTerm z m p) = liftM (SendTerm (var z) m) (replace' p)
          replace' (ReceiveTerm z i p) = liftM (ReceiveTerm (var z) i) (replace' p)
          replace' (EmptyOut z) = return (EmptyOut (var z))
          replace' (EmptyIn z p) = liftM (EmptyIn (var z)) (replace' p)
          replace' (EmptyCase z ws) = return (EmptyCase (var z) (map var ws))
          replace' (Quote m ds) = return (Quote m (replaceBindings `fmap` ds))
              where exn z | z == x = y
                          | otherwise = z
                    second f (x, y) = (x, f y)
                    replaceBindings ds = ds{ names = map (second exn) (names ds) }
          replace' (Unk vs) = return (Unk (map var vs))
          replace' p = error ("Replace missing case for " ++ show p)

--------------------------------------------------------------------------------
-- Recursion

class HasGVTranslation t
    where hasGVTranslation :: t -> Bool

instance HasGVTranslation Prop
    where hasGVTranslation (Univ _ a)    = hasGVTranslation a
          hasGVTranslation (Exist _ a)   = hasGVTranslation a
          hasGVTranslation Mu{}          = False
          hasGVTranslation Nu{}          = False
          hasGVTranslation (OfCourse a)  = hasGVTranslation a
          hasGVTranslation (WhyNot a)    = hasGVTranslation a
          hasGVTranslation (Times a b)   = hasGVTranslation a || hasGVTranslation b
          hasGVTranslation (Par a b)     = hasGVTranslation a || hasGVTranslation b
          hasGVTranslation One           = True
          hasGVTranslation Bottom        = True
          hasGVTranslation (Plus lts)    = any (hasGVTranslation . snd) lts
          hasGVTranslation (With lts)    = any (hasGVTranslation . snd) lts
          hasGVTranslation (Var s ps)    = any hasGVTranslation ps
          hasGVTranslation (Neg s)       = True
          hasGVTranslation (FOUniv _ p)  = False
          hasGVTranslation (FOExist _ p) = False
          hasGVTranslation (Dual p)      = hasGVTranslation p

instance HasGVTranslation Arg
    where hasGVTranslation (ProcArg p) = hasGVTranslation p
          hasGVTranslation NameArg{}   = True

instance HasGVTranslation Proc
    where hasGVTranslation (ProcVar _ args)    = any hasGVTranslation args
          hasGVTranslation Link{}              = True
          hasGVTranslation (Cut x a p q)       = hasGVTranslation a || hasGVTranslation p || hasGVTranslation q
          hasGVTranslation (Out _ _ p q)       = hasGVTranslation p || hasGVTranslation q
          hasGVTranslation (In _ _ p)          = hasGVTranslation p
          hasGVTranslation (Select _ _ p)      = hasGVTranslation p
          hasGVTranslation (Case _ bs)         = any (hasGVTranslation . snd) bs
          hasGVTranslation Unroll{}            = False
          hasGVTranslation Roll{}              = False
          hasGVTranslation (Replicate _ _ p)   = hasGVTranslation p
          hasGVTranslation (Derelict _ _ p)    = hasGVTranslation p
          hasGVTranslation (SendProp _ a p)    = hasGVTranslation a || hasGVTranslation p
          hasGVTranslation (ReceiveProp _ _ p) = hasGVTranslation p
          hasGVTranslation SendTerm{}          = False
          hasGVTranslation ReceiveTerm{}       = False
          hasGVTranslation EmptyOut{}          = True
          hasGVTranslation (EmptyIn _ p)       = hasGVTranslation p
          hasGVTranslation EmptyCase{}         = True
          hasGVTranslation Quote{}             = False
          hasGVTranslation Unk{}               = True

----------------------------------------------------------------------------------------------------
-- First-order structure

data FOType = Int | Bool | Unit | FOType `To` FOType | TQuote Behavior
    deriving (Eq, Show)
data FOTerm = EVar String | EInt Integer | EBool Bool | EUnit
            | EApp FOTerm FOTerm | ELam String FOType FOTerm
            | EIf FOTerm FOTerm FOTerm
            | EQuote Proc Behavior
            | EFix FOTerm
    deriving (Eq, Show)

channels :: FOTerm -> [String]
channels (EApp e e')    = channels e ++ channels e'
channels (ELam _ _ e)   = channels e
channels (EIf e e' e'') = concatMap channels [e, e', e'']
channels (EQuote p b)   = map fst b
channels (EFix e)       = channels e
channels _              = []
