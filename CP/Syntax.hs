{-# LANGUAGE TupleSections, GeneralizedNewtypeDeriving #-}
module CP.Syntax where

import Control.Monad
import Control.Monad.Error
import Control.Monad.State

data Prop = ForAll String Prop
          | Exists String Prop
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
          | Dual Prop
    deriving (Eq, Show)

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
          | EmptyOut String
          | EmptyIn String Proc
          | EmptyCase String [String]
          | Unk [String]
    deriving (Eq, Show)

data Defn = ProcDef String [Param] Proc
          | PropDef String [String] Prop
    deriving (Eq, Show)

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
fn (EmptyOut x)        = [x]
fn (EmptyIn x p)       = x : fn p
fn (EmptyCase x ys)    = x : ys
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
fln (EmptyOut x)        = [x]
fln (EmptyIn x p)       = x : fln p
fln (EmptyCase x ys)    = x : ys
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
          replace' (EmptyOut z) = return (EmptyOut (var z))
          replace' (EmptyIn z p) = liftM (EmptyIn (var z)) (replace' p)
          replace' (EmptyCase z ws) = return (EmptyCase (var z) (map var ws))
          replace' (Unk vs) = return (Unk (map var vs))
          replace' p = error ("Replace missing case for " ++ show p)

--------------------------------------------------------------------------------
-- Recursion

class RequiresRecursion t
    where requiresRecursion :: t -> Bool

instance RequiresRecursion Prop
    where requiresRecursion (ForAll _ a) = requiresRecursion a
          requiresRecursion (Exists _ a) = requiresRecursion a
          requiresRecursion Mu{}         = True
          requiresRecursion Nu{}         = True
          requiresRecursion (OfCourse a) = requiresRecursion a
          requiresRecursion (WhyNot a)   = requiresRecursion a
          requiresRecursion (Times a b)  = requiresRecursion a || requiresRecursion b
          requiresRecursion (Par a b)    = requiresRecursion a || requiresRecursion b
          requiresRecursion One          = False
          requiresRecursion Bottom       = False
          requiresRecursion (Plus lts)   = any (requiresRecursion . snd) lts
          requiresRecursion (With lts)   = any (requiresRecursion . snd) lts
          requiresRecursion (Var s ps)   = any requiresRecursion ps
          requiresRecursion (Neg s)      = False
          requiresRecursion (Dual p)     = requiresRecursion p

instance RequiresRecursion Arg
    where requiresRecursion (ProcArg p) = requiresRecursion p
          requiresRecursion NameArg{}   = False

instance RequiresRecursion Proc
    where requiresRecursion (ProcVar _ args)    = any requiresRecursion args
          requiresRecursion Link{}              = False
          requiresRecursion (Cut x a p q)       = requiresRecursion a || requiresRecursion p || requiresRecursion q
          requiresRecursion (Out _ _ p q)       = requiresRecursion p || requiresRecursion q
          requiresRecursion (In _ _ p)          = requiresRecursion p
          requiresRecursion (Select _ _ p)      = requiresRecursion p
          requiresRecursion (Case _ bs)         = any (requiresRecursion . snd) bs
          requiresRecursion Unroll{}            = True
          requiresRecursion Roll{}              = True
          requiresRecursion (Replicate _ _ p)   = requiresRecursion p
          requiresRecursion (Derelict _ _ p)    = requiresRecursion p
          requiresRecursion (SendProp _ a p)    = requiresRecursion a || requiresRecursion p
          requiresRecursion (ReceiveProp _ _ p) = requiresRecursion p
          requiresRecursion EmptyOut{}          = False
          requiresRecursion (EmptyIn _ p)       = requiresRecursion p
          requiresRecursion EmptyCase{}         = False
          requiresRecursion Unk{}               = False
