{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module GV.CPBuilder where

import Control.Monad
import CP.Syntax

type BuilderEnv = ([(String, String)], Int)
newtype V = V String
newtype Builder t = B{ runBuilder :: [(String, String)] -> Int -> (t, Int) }
instance Functor Builder
    where fmap f (B g) = B (\m z -> let (v, z') = g m z in (f v, z'))
instance Monad Builder
    where return v = B (\m z -> (v, z))
          B f >>= g = B (\m z -> let (v, z') = f m z
                                 in  runBuilder (g v) m z')

class ChannelName t
    where binder :: t -> (String -> Builder u) -> Builder u
          reference :: t -> Builder String
instance ChannelName String
    where binder v c = c v
          reference v = return v
instance ChannelName V
    where binder (V s) b = B (\m z -> let s' = s ++ '!' : show z
                                      in  runBuilder (b s') ((s, s'):m) (z + 1))
          reference (V s) = B (\m z -> case lookup s m of
                                         Just s' -> (s', z)
                                         Nothing -> (s, z))

link w x = liftM2 Link (reference w) (reference x)
nu x a m n = binder x (\x' -> liftM2 (Cut x' a) m n)
out x y m n  = do x' <- reference x
                  (y', m') <- binder y (\y' -> do m' <- m
                                                  return (y', m'))
                  liftM (Out x' y' m') n
in_ x y m = do x' <- reference x
               binder y (\y' -> liftM (In x' y') m)
inj x l m = liftM3 Select (reference x) (return l) m
case_ x bs = liftM2 Case (reference x) bs
rec x m = liftM2 Rec (reference x) m
corec x y a m n = binder y (\y' -> do x' <- reference x
                                      liftM2 (CoRec x' y' a) m n)
replicate x y m = do x' <- reference x
                     binder y (\y' -> liftM (Replicate x' y') m)
derelict x y m = do x' <- reference x
                    binder y (\y' -> liftM (Derelict x' y') m)
emptyOut x = liftM EmptyOut (reference x)
emptyIn x m = liftM2 EmptyIn (reference x) m
emptyCase x xs = do x' <- reference x
                    return (EmptyCase x' xs)
sendType x a m = do x' <- reference x
                    liftM (SendProp x' a) m
receiveType x z m = do x' <- reference x
                       liftM (ReceiveProp x' z) m
sendTerm x v m = do x' <- reference x
                    liftM (SendTerm x' v) m
receiveTerm x z m = do x' <- reference x
                       liftM (ReceiveTerm x' z) m
