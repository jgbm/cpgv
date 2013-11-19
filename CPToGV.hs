module CPToGV where

import Data.Maybe

import CheckGV (dual)

import qualified Check as CPCheck (dual)

import qualified Syntax.AbsCP as CP
import qualified Syntax.AbsGV as GV

xSession :: CP.Type -> GV.Session
xSession (CP.Times a b) = GV.Output (xTypeDual a) (xSession b)
xSession (CP.Par a b) = GV.Input (xType a) (xSession b)
xSession (CP.Zero) = GV.Sum []
xSession (CP.Plus cs) = GV.Sum (map (\(CP.Label x a) -> GV.Label (xId x) (xSession a)) cs)
xSession (CP.With cs) = GV.Choice (map (\(CP.Label x a) -> GV.Label (xId x) (xSession a)) cs)
xSession (CP.Top) = GV.Choice []
xSession (CP.One) = GV.OutTerm
xSession (CP.Bottom) = GV.InTerm
xSession (CP.OfCourse a) = GV.Server (xSession a)
xSession (CP.WhyNot a) = GV.Service (xSession a)
xSession (CP.Var (CP.UIdent a)) = GV.SVar (GV.UIdent a)

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
xTerm env (CP.Case x cs) =
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
xTerm env (CP.ServerAccept s x p) =
  GV.Serve (xId s) (xId x) (xTerm (extend env (x, xt)) p)
  where
    (CP.OfCourse xt) = find s env
xTerm env (CP.ClientRequest s x p) =
  GV.With (xId x) (xSession xt)
          (GV.Link (GV.Request (xId s)) (GV.Var (xId x)))
          (xTerm (extend env (x, xt)) p)
  where
    (CP.WhyNot xt) = find s env
xTerm env (CP.SendType _ _ _)      = error ("xTerm (SendType _ _ _) unimplemented")
xTerm env (CP.ReceiveType _ _ _)   = error ("xTerm (ReceiveType _ _ _) unimplemented")
xTerm env (CP.EmptyOut x)          = GV.Var (xId x)
xTerm env (CP.EmptyIn x p)         = GV.End (GV.Pair (xTerm (extend env (x, CP.Bottom)) p) (GV.Var (xId x)))
xTerm env (CP.EmptyCase x [])      = GV.Case (GV.Var (xId x)) []
