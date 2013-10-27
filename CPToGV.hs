module CPToGV where

import CheckGV (dual)

import qualified Syntax.AbsCP as CP
import qualified Syntax.AbsGV as GV

xSession :: CP.Type -> GV.Session
xSession (CP.Times a b) = GV.Input (xType a) (xSession b)
xSession (CP.Par a b) = GV.Output (xTypeDual a) (xSession b)
xSession (CP.Plus cs) = GV.Sum (map (\(CP.Label x a) -> GV.Label (xId x) (xSession a)) cs)
xSession (CP.With cs) = GV.Choice (map (\(CP.Label x a) -> GV.Label (xId x) (xSession a)) cs)
xSession (CP.One) = GV.InTerm
xSession (CP.Bottom) = GV.OutTerm 

xType :: CP.Type -> GV.Type
xType = GV.Lift . xSession

xTypeDual :: CP.Type -> GV.Type
xTypeDual = GV.Lift . dual . xSession

xId :: CP.LIdent -> GV.LIdent
xId (CP.LIdent s) = GV.LIdent s

xTerm :: CP.Proc -> GV.Term
xTerm (CP.ProcVar _)       = error ("xTerm (ProcVar _) unimplemented")
xTerm (CP.ProcVarArgs _ _) = error ("xTerm (ProcVarArgs _ _) unimplemented")
xTerm (CP.Link x y)        = error ("xTerm (Link _ _) unimplemented")
xTerm (CP.Comp x t p q)    = GV.With (xId x) (xSession t) (xTerm p) (xTerm q)
xTerm (CP.Out x y p q) =
  GV.With y' undefined
          (xTerm p)
          (GV.Let (GV.BindName x') (GV.Send (GV.Var y') (GV.Var x')) (xTerm q))
  where
    x' = xId x
    y' = xId y
xTerm (CP.In x y r) =
  GV.Let (GV.BindPair y' x') (GV.Receive (GV.Var x')) (xTerm r)
  where
    x' = xId x
    y' = xId y
xTerm (CP.Inj x l p) =
  GV.Let (GV.BindName x') (GV.Select l' (GV.Var x')) (xTerm p)
  where
    x' = xId x
    l' = xId l
xTerm (CP.Case x cs) =
  GV.Case (GV.Var x')
    (map (\(CP.Branch l p) -> GV.Branch (xId l) x' (xTerm p)) cs)
  where
    x' = xId x
xTerm (CP.ServerAccept _ _ _)  = error ("xTerm (ServerAccept _ _ _) unimplemented")
xTerm (CP.ClientRequest _ _ _) = error ("xTerm (ClientRequest _ _ _) unimplemented")
xTerm (CP.SendType _ _ _)      = error ("xTerm (SendType _ _ _) unimplemented")
xTerm (CP.ReceiveType _ _ _)   = error ("xTerm (ReceiveType _ _ _) unimplemented")
xTerm (CP.EmptyOut x)          = GV.Var (xId x)
xTerm (CP.EmptyIn x p)         = GV.End (GV.Pair (xTerm p) (GV.Var (xId x)))  
