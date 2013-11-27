module CPToGV where

import Data.Maybe

import CheckGV (dual)

import qualified Check as CPCheck (dual, inst)

import qualified Syntax.AbsCP as CP
import qualified Syntax.AbsGV as GV

xSession :: CP.Type -> GV.Session
xSession (CP.Times a b) = GV.Output (xTypeDual a) (xSession b)
xSession (CP.Par a b) = GV.Input (xType a) (xSession b)
xSession (CP.Plus cs) = GV.Sum (map (\(CP.Label x a) -> GV.Label (xId x) (xSession a)) cs)
xSession (CP.With cs) = GV.Choice (map (\(CP.Label x a) -> GV.Label (xId x) (xSession a)) cs)
-- xSession (CP.Zero) = GV.Sum []
-- xSession (CP.Top) = GV.Choice []
xSession (CP.One) = GV.OutTerm
xSession (CP.Bottom) = GV.InTerm
xSession (CP.OfCourse a) = GV.Server (xSession a)
xSession (CP.WhyNot a) = GV.Service (xSession a)
xSession (CP.Var (CP.UIdent v)) = GV.SVar (GV.UIdent v)
xSession (CP.Neg (CP.UIdent v)) = GV.Neg (GV.UIdent v)
xSession (CP.ForAll (CP.UIdent v) a) = GV.InputType (GV.UIdent v) (xSession a)
xSession (CP.Exists (CP.UIdent v) a) = GV.OutputType (GV.UIdent v) (xSession a)

xType :: CP.Type -> GV.Type
xType = GV.Lift . xSession

xTypeDual :: CP.Type -> GV.Type
xTypeDual = GV.Lift . dual . xSession

xId :: CP.LIdent -> GV.LIdent
xId (CP.LIdent s) = GV.LIdent s

type TypeEnv = [(CP.LIdent, CP.Type)]

extend :: TypeEnv -> (CP.LIdent, CP.Type) -> TypeEnv
extend = flip (:)

find x env = fromJust (lookup x env)

xTerm :: TypeEnv -> CP.Proc -> GV.Term
xTerm env (CP.ProcVar _)       = error ("xTerm (ProcVar _) unimplemented")
xTerm env (CP.ProcVarArgs _ _) = error ("xTerm (ProcVarArgs _ _) unimplemented")
xTerm env (CP.Link x y)      = GV.Link (GV.Var (xId x)) (GV.Var (xId y))
xTerm env (CP.Comp x t p q)  = GV.With (xId x) (xSession t)
                                       (xTerm (extend env (x, t)) p)
                                       (xTerm (extend env (x, CPCheck.dual t)) q)
xTerm env (CP.Out x y p q) =
  GV.With y' (xSession yt)
          (xTerm (extend env (y, yt)) p)
          (GV.Let (GV.BindName x') (GV.Send (GV.Var y') (GV.Var x')) (xTerm (extend env (x, xt)) q))
  where
    x' = xId x
    y' = xId y
    (yt `CP.Times` xt) = find x env
xTerm env (CP.In x y r) =
  GV.Let (GV.BindPair y' x') (GV.Receive (GV.Var x')) (xTerm (extend (extend env (y,yt)) (x, xt)) r)
  where
    x' = xId x
    y' = xId y
    (yt `CP.Par` xt) = find x env
xTerm env (CP.Inj x l p) =
  GV.Let (GV.BindName x') (GV.Select l' (GV.Var x')) (xTerm (extend env (x, xt)) p)
  where
    x' = xId x
    l' = xId l
    (CP.Plus lts) = find x env
    xt = findLabel l lts
    findLabel l (CP.Label l' t : lts)
      | l == l'   = t
      | otherwise = findLabel l lts
xTerm env (CP.Case x cs@(_:_)) =
  GV.Case (GV.Var x')
    (map (\(CP.Branch l p) -> branch l p) cs)
  where
    x' = xId x
    branch l p = GV.Branch (xId l) x' (xTerm (extend env (x, xt)) p)
      where
        (CP.With lts) = find x env
        xt = findLabel l lts
    findLabel l (CP.Label l' t : lts)
      | l == l'   = t
      | otherwise = findLabel l lts
xTerm env (CP.EmptyCase x xs) =
  GV.EmptyCase (GV.Var (xId x)) (map xId xs) (GV.Lift GV.InTerm)
xTerm env (CP.ServerAccept s x p) =
  GV.Serve (xId s) (xId x) (xTerm (extend env (x, xt)) p)
  where
    (CP.OfCourse xt) = find s env
xTerm env (CP.ClientRequest s x p) =
  GV.With (xId x) (dual (xSession xt))
          (GV.Link (GV.Request (xId s)) (GV.Var (xId x)))
          (xTerm (extend env (x, xt)) p)
  where
    (CP.WhyNot xt) = find s env
xTerm env (CP.SendType x a p)      =
  GV.Let (GV.BindName x') (GV.SendType (xSession a) (GV.Var x')) (xTerm (extend env (x, xt)) p)
  where
    x' = xId x
    (CP.Exists v t) = find x env
    xt = CPCheck.inst v a t
xTerm env (CP.ReceiveType x v p)   =
  GV.Let (GV.BindName x') (GV.ReceiveType (GV.Var x')) (xTerm (extend env (x, xt)) p)
  where
    x' = xId x
    (CP.ForAll v xt) = find x env
xTerm env (CP.EmptyOut x)          = GV.Var (xId x)
xTerm env (CP.EmptyIn x p)         = GV.Let GV.BindUnit (GV.End (GV.Var (xId x))) (xTerm env p)
