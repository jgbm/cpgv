{-# LANGUAGE PatternGuards, TupleSections #-}
module GVToCP where

import Data.Maybe

import Prelude hiding (replicate)
import Data.List hiding (replicate, find)

import qualified CP.Syntax as CP
import qualified GV.Syntax as GV
import GV.Printer
import GV.Syntax (dual)

import GV.CPBuilder

xSession :: GV.Session -> CP.Prop
xSession (GV.Output t s)     = CP.dual (xType t) `CP.Par` xSession s
xSession (GV.Input t s)      = xType t `CP.Times` xSession s
xSession (GV.Sum cs)         = CP.With [(l, xSession st) | (l, st) <- cs]
xSession (GV.Choice cs)      = CP.Plus [(l, xSession st) | (l, st) <- cs]
xSession GV.OutTerm          = CP.Bottom
xSession GV.InTerm           = CP.One
xSession (GV.Mu x s)         = CP.Nu x (xSession s)
xSession (GV.Nu x s)         = CP.Mu x (xSession s)
xSession (GV.Server s)       = CP.WhyNot (xSession s)
xSession (GV.Service s)      = CP.OfCourse (xSession s)
xSession (GV.SVar s)         = CP.Var s []
xSession (GV.Neg s)          = CP.Neg s
xSession (GV.OutputType x s) = CP.Exist x (xSession s)
xSession (GV.InputType x s)  = CP.Univ x (xSession s)

xType :: GV.Type -> CP.Prop
xType (GV.Lift s)     = xSession s
xType (GV.LinFun t u) = CP.dual (xType t) `CP.Par` xType u
xType (GV.UnlFun t u) = CP.OfCourse (xType (GV.LinFun t u))
xType (GV.Tensor t u) = xType t `CP.Times` xType u
xType GV.UnitType     = CP.OfCourse (CP.With [])
xType GV.Int          = CP.OfCourse (CP.FOExist CP.Int CP.One)

type TypeEnv = [(String, GV.Type)]

extend :: TypeEnv -> (String, GV.Type) -> TypeEnv
extend = flip (:)

find x env = fromJust (lookup x env)

-- TODO: fill in recursive/corecursive voodoo

xTerm :: TypeEnv -> GV.Term -> (GV.Type, String -> Builder CP.Proc)
xTerm env GV.Unit = (GV.UnitType, \z -> replicate z (V "y") (emptyCase (V "y") []))
xTerm env (GV.EInt n) =
  (GV.Int, \z -> replicate z x 
                    (nu y (CP.Bottom)
                        (sendTerm x (CP.EInt n) (link x y))
                        (emptyOut y)))
  where x = V "x"
        y = V "y"
xTerm env (GV.Var x) = (find x env, \z -> link x z)
xTerm env (GV.Link m n) =
  (GV.Lift GV.OutTerm,
   \z -> nu (V "x") (xSession s)                    
            (m' =<< reference (V "x"))              
            (nu (V "y") (xSession s')               
                (n' =<< reference (V "y"))          
                (emptyIn z (link (V "x") (V "y")))))
  where
    (GV.Lift s, m') = xTerm env m
    (GV.Lift s', n') = xTerm env n
xTerm env (GV.UnlLam x t m) =
  (GV.UnlFun t u, \z -> replicate z (V "y") (in_ (V "y") x (m' =<< reference (V "y"))))
  where
    (u, m') = xTerm (extend env (x, t)) m
xTerm env (GV.LinLam x t m) =
  (GV.LinFun t u, \z -> in_ z x (m' z))
  where
    (u, m') = xTerm (extend env (x, t)) m
xTerm env (GV.App m n) =
  case mty of
    v `GV.LinFun` w -> (w, \z -> nu (V "w") (xType mty)
                                    (m' =<< reference (V "w")) (out (V "w") (V "x")
                                    (n' =<< reference (V "x")) (link (V "w") z)))
    v `GV.UnlFun` w -> (w, \z -> nu (V "y") (xType (v `GV.LinFun` w))
                                    (nu (V "w") (xType (v `GV.UnlFun` w))
                                        (m' =<< reference (V "w"))
                                        (derelict (V "w") (V "x") (link (V "x") (V "y"))))
                                    (out (V "y") (V "x") (n' =<< reference (V "x")) (link (V "y") z)))
  where
    (mty, m') = xTerm env m
    (_,   n') = xTerm env n
xTerm env (GV.Pair m n) =
  (GV.Tensor mty nty, \z -> out z (V "y") (m' =<< reference (V "y")) (n' z))
  where
    (mty, m') = xTerm env m
    (nty, n') = xTerm env n
xTerm env (GV.Let (GV.BindName x) m n) =
  let (t, m') = xTerm env m in
  let (u, n') = xTerm (extend env (x, t)) n in
  -- weakening for end?
  if t == GV.Lift GV.InTerm && x `notElem` GV.fv n
  then (u, \z -> nu x (xType t) (m' =<< reference x) (emptyIn x (n' z)))
  else (u, \z -> nu x (xType t) (m' =<< reference x) (n' z))
xTerm env (GV.Let (GV.BindPair x y) m n) =
  let (mty@(GV.Tensor xty yty), m') = xTerm env m
      isWeakened z zty = if zty == GV.Lift GV.InTerm && z `notElem` GV.fv n then (z :) else id
      weakened = isWeakened x xty (isWeakened y yty [])
      (nty, n') = xTerm (extend (extend env (x, xty)) (y, yty)) n
  in
    (nty, \z -> nu y (xType mty) (m' =<< reference y) (in_ y x (foldr emptyIn (n' z) weakened)))
xTerm env (GV.LetRec (x,b) f ps c m n) = undefined
xTerm env (GV.Corec c ci ts m n) = undefined
xTerm env (GV.Send m n) =
  let (mty, m') = xTerm env m
      (GV.Lift (GV.Output v w), n') = xTerm env n
  in
      (GV.Lift w, \z -> nu (V "x") (xType v `CP.Times` CP.dual (xSession w))
                           (out (V "x") (V "y") (m' =<< reference (V "y"))
                           (link (V "x") z)) (n' =<< reference (V "x")))
xTerm env (GV.Receive m) =
  let (GV.Lift (GV.Input v w), m') = xTerm env m in
    (v `GV.Tensor` GV.Lift w, m')
xTerm env (GV.Select l m) =
  let (mty@(GV.Lift (GV.Sum cs)), m') = xTerm env m in
    (GV.Lift (find l cs),
     \z -> nu (V "x") (xType mty)
              (m' =<< reference (V "x"))
              (inj (V "x") l (link (V "x") z)))
xTerm env (GV.Case m bs@(_:_)) =
  let (mty@(GV.Lift (GV.Choice cs)), m') = xTerm env m 
      (t:_, bs') = unzip (map (xBranch env cs) bs)
  in
    (t, 
     \z -> nu (V "x") (xType mty)
              (m' =<< reference (V "x"))
              (case_ (V "x") (sequence [reference (V "x") >>= flip b' z | b' <- bs'])))
  where
    xBranch :: TypeEnv -> [(String, GV.Session)] ->
                 (String, String, GV.Term) -> (GV.Type, String -> String -> Builder (String, CP.Proc))
    xBranch env cs (l, x, n) =
      let s = find l cs
          (t, n') = xTerm (extend env (x, GV.Lift s)) n
      in
          (t, \y z -> ((l,) . replace x y) `fmap` checkWeakening x t n (n' z))

    checkWeakening x t n p
         | t == GV.Lift GV.InTerm && x `notElem` GV.fv n = emptyIn x p
         | otherwise = p

    replace x y t = t'
      where Right t' = CP.runM (CP.replace x y t)
    
xTerm env (GV.EmptyCase m xs t) =
  let (mty@(GV.Lift (GV.Choice [])), m') = xTerm env m in
    (t, \z -> nu (V "x") (xType mty)
                 (m' =<< reference (V "x"))
                 (emptyCase (V "x") xs))
xTerm env (GV.Fork x a m) =
  let (mty@(GV.Lift GV.OutTerm), m') = xTerm (extend env (x, GV.Lift a)) m in
    (GV.Lift (dual a),
     \z -> nu x (xSession (dual a))
              (nu (V "y") CP.Bottom (m' =<< reference (V "y")) (emptyOut (V "y")))
              (link x z))
xTerm env (GV.Serve x a m) =
  let (t@(GV.Lift GV.OutTerm), m') = xTerm (extend env (x, GV.Lift a)) m in
    (GV.Lift (dual a),
     \z -> nu x (xSession (dual a))
              (nu (V "y") CP.Bottom (m' =<< reference (V "y")) (emptyOut (V "y")))
              (link x z))
xTerm env (GV.Request m) =
  let (t@(GV.Lift (GV.Service ty)), m') = xTerm env m in
    (GV.Lift ty,
     \z -> nu (V "x") (CP.OfCourse (xSession ty))
              (m' =<< reference (V "x"))
              (derelict (V "x") (V "y") (link (V "y") z)))
xTerm env (GV.SendType s m) =
  let (mty@(GV.Lift (GV.OutputType v s')), m') = xTerm env m in
    (GV.Lift (GV.instSession v s s'),
     \z -> nu (V "x") (CP.dual (xType mty))
              (sendType (V "x") (xSession s) (link (V "x") z))
              (m' =<< reference (V "x")))
xTerm env (GV.ReceiveType m) =
  let (mty@(GV.Lift (GV.InputType v s')), m') = xTerm env m in
    (GV.Lift s',
     \z -> nu (V "x") (CP.dual (xType mty))
              (receiveType (V "x") v (link (V "x") z))
              (m' =<< reference (V "x")))
