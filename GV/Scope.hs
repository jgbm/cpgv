{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}
module GV.Scope (renameTerm) where

import Control.Monad
import GV.Syntax

type Environment = ([(String, String)], Int)
newtype ScopeM t = Scope { runScope :: Environment -> t }
instance Functor ScopeM
    where fmap f (Scope g) = Scope (f . g)
instance Monad ScopeM
    where return v = Scope (const v)
          Scope f >>= g = Scope (\e -> runScope (g (f e)) e)

reference x = Scope (\(e,z) -> case lookup x e of
                                 Nothing -> x
                                 Just x' -> x')

binder x v = Scope (\(e,z) -> let x' = (x ++ '-' : show z)
                              in  runScope (v x') ((x, x') : e, z + 1))

class HasScopedVariables t
    where rename :: t -> ScopeM t

instance HasScopedVariables Term
    where rename (Var v) = liftM Var (reference v)
          rename (Link m n) = liftM2 Link (rename m) (rename n)
          rename (LinLam x t m) = binder x (\x' -> LinLam x' t `fmap` rename m)
          rename (UnlLam x t m) = binder x (\x' -> UnlLam x' t `fmap` rename m)
          rename (App m n) = liftM2 App (rename m) (rename n)
          rename (Pair m n) = liftM2 Pair (rename m) (rename n)
          rename (Let p m n) =
              do m' <- rename m
                 case p of
                   BindName x   -> binder x (\x' -> Let (BindName x') m' `fmap` rename n)
                   BindPair x y -> binder x (\x' -> binder y (\y' -> Let (BindPair x' y') m' `fmap` rename n))
          rename (Send m n) = liftM2 Send (rename m) (rename n)
          rename (Receive m) = liftM Receive (rename m)
          rename (Select l m) = liftM (Select l) (rename m)
          rename (Case m bs) = liftM2 Case (rename m) (mapM renameBranch bs)
              where renameBranch (l, x, m) = binder x (\x' -> liftM (l, x',) (rename m))
          rename (Fork x t m) = binder x (\x' -> liftM (Fork x' t) (rename m))
          rename (Serve x t m) = binder x (\x' -> liftM (Serve x' t) (rename m))
          rename (Request m) = liftM Request (rename m)

renameTerm m = runScope (rename m) ([], 1)
