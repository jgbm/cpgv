{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ScopeGV (renameTerm) where

import Control.Monad
import Syntax.AbsGV

type Environment = ([(String, String)], Int)
newtype ScopeM t = Scope { runScope :: Environment -> t }
instance Functor ScopeM
    where fmap f (Scope g) = Scope (f . g)
instance Monad ScopeM
    where return v = Scope (const v)
          Scope f >>= g = Scope (\e -> runScope (g (f e)) e)

reference (LIdent x) = Scope (\(e,z) -> case lookup x e of
                                          Nothing -> (LIdent x)
                                          Just x' -> (LIdent x'))

binder (LIdent x) v = Scope (\(e,z) -> let x' = (x ++ '-' : show z)
                                       in  runScope (v (LIdent x')) ((x, x') : e, z + 1))

class HasScopedVariables t
    where rename :: t -> ScopeM t

instance HasScopedVariables Term
    where rename (Var v) = liftM Var (reference v)
          rename Unit = return Unit
          rename (Link m n) = liftM2 Link (rename m) (rename n)
          rename (LinLam x t m) = binder x (\x' -> LinLam x' t `fmap` rename m)
          rename (UnlLam x t m) = binder x (\x' -> UnlLam x' t `fmap` rename m)
          rename (App m n) = liftM2 App (rename m) (rename n)
          rename (Pair m n) = liftM2 Pair (rename m) (rename n)
          rename (Let p m n) =
              do m' <- rename m
                 case p of
                   BindName x   -> binder x (\x' -> Let (BindName x') m' `fmap` rename n)
                   BindUnit     -> Let BindUnit m' `fmap` rename n
                   BindPair x y -> binder x (\x' -> binder y (\y' -> Let (BindPair x' y') m' `fmap` rename n))
          rename (Send m n) = liftM2 Send (rename m) (rename n)
          rename (Receive m) = liftM Receive (rename m)
          rename (Select l m) = liftM (Select l) (rename m)
          rename (Case m bs) = liftM2 Case (rename m) (mapM renameBranch bs)
              where renameBranch (Branch l x m) = binder x (\x' -> liftM (Branch l x') (rename m))
          rename (With x t m n) = binder x (\x' -> liftM2 (With x' t) (rename m) (rename n))
          rename (End m) = liftM End (rename m)
          rename (Serve x y m) = do x' <- reference x
                                    binder y (\y' -> liftM (Serve x' y') (rename m))
          rename (Request v) = liftM Request (reference v)

renameTerm m = runScope (rename m) ([], 1)
