{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module CPBuilder where

import Control.Monad
import Syntax.AbsCP

type BuilderEnv = ([(String, String)], Int)
newtype Builder t = B{ runBuilder :: [(String, String)] -> Int -> (t, Int) }
instance Functor Builder
    where fmap f (B g) = B (\m z -> let (v, z') = g m z in (f v, z'))
instance Monad Builder
    where return v = B (\m z -> (v, z))
          B f >>= g = B (\m z -> let (v, z') = f m z
                                 in  runBuilder (g v) m z')

class ChannelName t
    where binder :: t -> (LIdent -> Builder u) -> Builder u
          reference :: t -> Builder LIdent
instance ChannelName LIdent
    where binder v c = c v
          reference v = return v
instance ChannelName String
    where binder s b = B (\m z -> let s' = s ++ '\'' : show z
                                  in  runBuilder (b (LIdent s')) ((s, s'):m) (z + 1))
          reference s = B (\m z -> case lookup s m of
                                     Just s' -> (LIdent s', z)
                                     Nothing -> (LIdent s, z))

link w x = liftM2 Link (reference w) (reference x)
nu x a m n = binder x (\x' -> liftM2 (Comp x' a) m n)
out x y m n  = do x' <- reference x
                  (y', m') <- binder y (\y' -> do m' <- m
                                                  return (y', m'))
                  liftM (Out x' y' m') n
--in_ :: (ChannelName t, ChannelName u) => t -> u -> Builder Proc -> Builder Proc
in_ x y m = do x' <- reference x
               binder y (\y' -> liftM (In x' y') m)
inj x l m = liftM3 Inj (reference x) (return l) m
case_ x bs = liftM2 Case (reference x) bs
accept x y m = do x' <- reference x
                  binder y (\y' -> liftM (ServerAccept x' y') m)
request x y m = do x' <- reference x
                   binder y (\y' -> liftM (ClientRequest x' y') m)
emptyOut x = liftM EmptyOut (reference x)
emptyIn x m = liftM2 EmptyIn (reference x) m
emptyCase x xs = do x' <- reference x
                    return (EmptyCase x' xs)


sendType x a m = do x' <- reference x
                    liftM (SendType x' a) m
receiveType x z m = do x' <- reference x
                       liftM (ReceiveType x' z) m
