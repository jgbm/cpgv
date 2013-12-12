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

-- Alpha-conversion

newtype M t = M { unM :: StateT Int (Either String) t }
    deriving (Functor, Monad, MonadPlus, MonadState Int, MonadError String)

runM = flip evalStateT 0 . unM

fresh s = do z <- get
             put (z + 1)
             return (takeWhile ('\'' /=) s ++ '\'' : show z)

replace :: String -> String -> Proc -> M Proc
replace x y = replace'
    where var z
              | x == z = y
              | otherwise = z

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
