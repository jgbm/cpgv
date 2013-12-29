module CPToGV where

import Data.Maybe

import qualified CP.Check as CPCheck (dual, inst)

import qualified CP.Syntax as CP
import CP.Printer
import GV.Syntax (dual)
import qualified GV.Syntax as GV

xSession :: CP.Prop -> GV.Session
xSession (CP.Times a b) = GV.Output (xTypeDual a) (xSession b)
xSession (CP.Par a b) = GV.Input (xType a) (xSession b)
xSession (CP.Plus cs) = GV.Sum (map (\(x, a) -> (x, xSession a)) cs)
xSession (CP.With cs) = GV.Choice (map (\(x, a) -> (x, xSession a)) cs)
xSession (CP.One) = GV.OutTerm
xSession (CP.Bottom) = GV.InTerm
xSession (CP.OfCourse a) = GV.Server (xSession a)
xSession (CP.WhyNot a) = GV.Service (xSession a)
xSession (CP.Var v []) = GV.SVar v
xSession (CP.Neg v) = GV.Neg v
xSession (CP.ForAll v a) = GV.InputType v (xSession a)
xSession (CP.Exists v a) = GV.OutputType v (xSession a)
xSession s = error ("xSession missing " ++ show s)

xType :: CP.Prop -> GV.Type
xType = GV.Lift . xSession

xTypeDual :: CP.Prop -> GV.Type
xTypeDual = GV.Lift . dual . xSession

xId = id

type TypeEnv = [(String, CP.Prop)]

extend :: TypeEnv -> (String, CP.Prop) -> TypeEnv
extend = flip (:)

find x env = fromJust (lookup x env)

xTerm :: TypeEnv -> CP.Proc -> GV.Term
xTerm env (CP.ProcVar x [])  = GV.Var x
xTerm env (CP.Link x y)      = GV.Link (GV.Var x) (GV.Var y)
xTerm env (CP.Cut x t p q)   = GV.Let (GV.BindName x)
                                      (GV.Fork x (xSession t) (xTerm (extend env (x, t)) p))
                                      (xTerm (extend env (x, CPCheck.dual t)) q)
xTerm env (CP.Out x y p q) =
  GV.Let (GV.BindName x)
         (GV.Send (GV.Fork y (xSession yt) (xTerm (extend env (y, yt)) p)) (GV.Var x))
         (xTerm (extend env (x, xt)) q)
  where
    (yt `CP.Times` xt) = find x env
xTerm env (CP.In x y r) =
  GV.Let (GV.BindPair y x) (GV.Receive (GV.Var x)) (xTerm (extend (extend env (y,yt)) (x, xt)) r)
  where
    (yt `CP.Par` xt) = find x env
xTerm env (CP.Select x l p) =
  GV.Let (GV.BindName x) (GV.Select l (GV.Var x)) (xTerm (extend env (x, xt)) p)
  where
    (CP.Plus lts) = find x env
    xt = findLabel l lts
    findLabel l ((l', t) : lts)
      | l == l'   = t
      | otherwise = findLabel l lts
xTerm env (CP.Case x cs@(_:_)) =
  GV.Case (GV.Var x)
    (map (\(l, p) -> branch l p) cs)
  where
    branch l p = (xId l, x, xTerm (extend env (x, xt)) p)
      where
        (CP.With lts) = find x env
        xt = findLabel l lts
    findLabel l ((l', t) : lts)
      | l == l'   = t
      | otherwise = findLabel l lts
xTerm env (CP.EmptyCase x xs) =
  GV.EmptyCase (GV.Var (xId x)) (map xId xs) (GV.Lift GV.OutTerm)
xTerm env (CP.Replicate s x p) =
  GV.Link (GV.Var s) (GV.Serve x (xSession xt) (xTerm (extend env (x, xt)) p))
  where
    (CP.OfCourse xt) = find s env
xTerm env (CP.Derelict s x p) =
  GV.Let (GV.BindName x)
         (GV.Fork x (dual (xSession xt)) (GV.Link (GV.Var x) (GV.Request (GV.Var s))))
         (xTerm (extend env (x, xt)) p)
  where
    (CP.WhyNot xt) = find s env
xTerm env (CP.SendProp x a p)      =
  GV.Let (GV.BindName x') (GV.SendType (xSession a) (GV.Var x')) (xTerm (extend env (x, xt)) p)
  where
    x' = xId x
    (CP.Exists v t) = find x env
    xt = CPCheck.inst v a t
xTerm env (CP.ReceiveProp x v p)   =
  GV.Let (GV.BindName x') (GV.ReceiveType (GV.Var x')) (xTerm (extend env (x, xt)) p)
  where
    x' = xId x
    (CP.ForAll v xt) = find x env
xTerm env (CP.EmptyOut x)          = GV.Var (xId x)
xTerm env (CP.EmptyIn x p)         = xTerm env p
xTerm _ t = error $ "No xTerm case for " ++ show (pretty t)