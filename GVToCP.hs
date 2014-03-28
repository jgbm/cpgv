{-# LANGUAGE PatternGuards, TupleSections #-}
module GVToCP where

import Data.Maybe

import Prelude hiding (replicate)
import Data.List hiding (replicate, find)

import qualified CP.Syntax as CP
import GV.Syntax
import GV.Printer
import GV.Syntax (dual)

import GV.CPBuilder

xSession :: Session -> CP.Prop
xSession (Output t s)     = CP.dual (xType t) `CP.Par` xSession s
xSession (Input t s)      = xType t `CP.Times` xSession s
xSession (Sum cs)         = CP.With [(l, xSession st) | (l, st) <- cs]
xSession (Choice cs)      = CP.Plus [(l, xSession st) | (l, st) <- cs]
xSession OutTerm          = CP.Bottom
xSession InTerm           = CP.One
xSession (Mu x s)         = CP.Nu x (xSession s)
xSession (Nu x s)         = CP.Mu x (xSession s)
xSession (Server s)       = CP.WhyNot (xSession s)
xSession (Service s)      = CP.OfCourse (xSession s)
xSession (SVar s)         = CP.Var s []
xSession (Neg s)          = CP.Neg s
xSession (OutputType x s) = CP.Exist x (xSession s)
xSession (InputType x s)  = CP.Univ x (xSession s)

xType :: Type -> CP.Prop
xType (Lift s)     = xSession s
xType (LinFun t u) = CP.dual (xType t) `CP.Par` xType u
xType (UnlFun t u) = CP.OfCourse (xType (LinFun t u))
xType (Tensor t u) = xType t `CP.Times` xType u
xType UnitType     = CP.OfCourse (CP.With [])
xType Int          = CP.OfCourse (CP.FOExist CP.Int CP.One)

type TypeEnv = [(String, Type)]

extend :: TypeEnv -> (String, Type) -> TypeEnv
extend = flip (:)

find x env = fromJust (lookup x env)

newtype Trans t = T { runTrans :: (TypeEnv, Int) -> (t, Int) }
instance Functor Trans
    where fmap f (T g) = T (\e -> let (v, i) = g e in (f v, i))
instance Monad Trans
    where return x = T (\(e, i) -> (x, i))
          T f >>= g = T (\(e, i) -> 
                            let (v, j) = f (e, i) in
                                runTrans (g v) (e, j))
          fail s = error s

provide :: String -> Type -> Trans t -> Trans t
provide x t (T f) = T (\(e, i) -> f (extend e (x, t), i))

consume :: String -> Trans Type
consume x = T (\(e, i) -> (find x e, i))

fresh :: String -> Trans String
fresh s = T (\(e, i) -> (s ++ '$' : show i, i+1))

xTerm :: Term -> Trans (Type, String -> Builder CP.Proc)
xTerm Unit = return (UnitType, \z -> replicate z (V "y") (emptyCase (V "y") []))
xTerm (EInt n) =
  return (Int, \z -> replicate z x 
                    (nu y (CP.Bottom)
                        (sendTerm x (CP.EInt n) (link x y))
                        (emptyOut y)))
  where x = V "x"
        y = V "y"
xTerm (Var x) = do t <- consume x
                   return (t, \z -> link x z)
xTerm (Link m n) =
  do (Lift s, m') <- xTerm m 
     (Lift s', n') <- xTerm n
     return (Lift OutTerm,
             \z -> nu (V "x") (xSession s)                    
                      (m' =<< reference (V "x"))              
                      (nu (V "y") (xSession s')               
                          (n' =<< reference (V "y"))          
                          (emptyIn z (link (V "x") (V "y")))))  
xTerm (UnlLam x t m) =
  do (u, m') <- provide x t (xTerm m)
     return (UnlFun t u,
             \z -> replicate z (V "y") (in_ (V "y") x (m' =<< reference (V "y"))))
xTerm (LinLam x t m) =
  do (u, m') <- provide x t (xTerm m)
     return (LinFun t u, \z -> in_ z x (m' z))
xTerm (App m n) =
  do (mty, m') <- xTerm m
     (_,   n') <- xTerm n
     case mty of
       v `LinFun` w -> return (w, \z -> nu (V "w") (xType mty)
                                              (m' =<< reference (V "w")) (out (V "w") (V "x")
                                              (n' =<< reference (V "x")) (link (V "w") z)))
       v `UnlFun` w -> return (w, \z -> nu (V "y") (xType (v `LinFun` w))
                                              (nu (V "w") (xType (v `UnlFun` w))
                                                          (m' =<< reference (V "w"))
                                                          (derelict (V "w") (V "x") (link (V "x") (V "y"))))
                                              (out (V "y") (V "x") (n' =<< reference (V "x")) (link (V "y") z)))
xTerm (Pair m n) =
  do (mty, m') <- xTerm m
     (nty, n') <- xTerm n
     return (Tensor mty nty, 
             \z -> out z (V "y") (m' =<< reference (V "y")) (n' z))
xTerm (Let (BindName x) m n) =
  do (t, m') <- xTerm m
     (u, n') <- provide x t (xTerm n)
     -- weakening for end?
     if t == Lift InTerm && x `notElem` fv n
     then return (u, \z -> nu x (xType t) (m' =<< reference x) (emptyIn x (n' z)))
     else return (u, \z -> nu x (xType t) (m' =<< reference x) (n' z))
xTerm (Let (BindPair x y) m n) =
  do (mty@(Tensor xty yty), m') <- xTerm m
     let isWeakened z zty = if zty == Lift InTerm && z `notElem` fv n then (z :) else id
         weakened = isWeakened x xty (isWeakened y yty [])
     (nty, n') <- provide x xty (provide y yty (xTerm n))
     return (nty, \z -> nu y (xType mty) (m' =<< reference y) (in_ y x (foldr emptyIn (n' z) weakened)))

xTerm (LetRec (x,b) f ps c m n) =
  do q <- fresh "Q"
     ci <- fresh "ci"
     (mty@(Lift OutTerm), _) <-
       provide f (foldr UnlFun (Lift (SVar q) `UnlFun` Lift OutTerm) ts) $
       provide c (Lift (instSession x (SVar q) b)) $
       foldr (\(x, t) m -> provide x t m) (xTerm m) ps
     (nty, _) <- provide f (foldr UnlFun (Lift (Nu x b) `UnlFun` Lift OutTerm) ts) (xTerm n)
     cis <- mapM (const (fresh "ci")) vs
     let m' = Let (BindName f)
                  ((foldr (\(v, t) rest m -> UnlLam v t (rest (Send (Var v) m)))
                          (UnlLam c (Lift (foldr Output OutTerm ts)))
                          ps) (Var c))
                  (foldr (\(v, ci1, ci2) m -> Let (BindPair v ci2) (Receive (Var ci1)) m)
                         m
                         (zip3 vs (ci:cis) cis))
         n' = Let (BindName f)
                  (foldr (\(v, t) m -> UnlLam v t m)
                         (UnlLam c (Lift (Nu x b)) (Corec c ci ts
                                                          (foldl (\m v -> Send (Var v) m) (Var ci) vs)
                                                          m'))
                         ps)
                  n
     (_, n'') <- xTerm n'
     return (nty, n'')
  where (vs, ts) = unzip ps
xTerm (Corec c ci ts m n) =
  do (cty@(Lift (Nu x b))) <- consume c
     (mty@(Lift OutTerm), m') <- provide x (Lift tsOut) (xTerm m)
     (nty@(Lift OutTerm), n') <- provide ci (Lift tsIn) (provide c (Lift (instSession x tsOut b)) (xTerm n))
     let mterm = nu (V "z") CP.One (emptyOut (V "z")) (m' =<< reference (V "z"))
         ciWeakened = tsIn == InTerm || ci `notElem` fv n
         nterm | ciWeakened = nu (V "z") CP.One (emptyOut (V "z")) (emptyIn ci (n' =<< reference (V "z")))
               | otherwise = nu (V "z") CP.One (emptyOut (V "z")) (n' =<< reference (V "z"))
     return (Lift OutTerm,
             \z -> emptyIn z (roll c ci (foldr CP.Times CP.One (map xType ts)) mterm nterm))
  where tsOut = foldr Output OutTerm ts
        tsIn  = foldr Input InTerm ts

xTerm (Send m n) =
  do (mty, m') <- xTerm m
     (Lift (Output v w), n') <- xTerm n
     return (Lift w,
             \z -> nu (V "x") (xType v `CP.Times` CP.dual (xSession w))
                      (out (V "x") (V "y") (m' =<< reference (V "y"))
                      (link (V "x") z)) (n' =<< reference (V "x")))
xTerm (Receive m) =
  do (Lift (Input v w), m') <- xTerm m
     return (v `Tensor` Lift w, m')
xTerm (Select l m) =
  do (mty@(Lift (Sum cs)), m') <- xTerm m
     return (Lift (find l cs),
             \z -> nu (V "x") (xType mty)
                      (m' =<< reference (V "x"))
                      (inj (V "x") l (link (V "x") z)))
xTerm (Case m bs@(_:_)) =
  do (mty@(Lift (Choice cs)), m') <- xTerm m 
     (t:_, bs') <- unzip `fmap` sequence (map (xBranch cs) bs)
     return (t, 
             \z -> nu (V "x") (xType mty)
                      (m' =<< reference (V "x"))
                      (case_ (V "x") (sequence [reference (V "x") >>= flip b' z | b' <- bs'])))
  where
    xBranch :: [(String, Session)] ->
                 (String, String, Term) -> Trans (Type, String -> String -> Builder (String, CP.Proc))
    xBranch cs (l, x, n) =
      let s = find l cs in
        do (t, n') <- provide x (Lift s) (xTerm n)
           return (t, \y z -> ((l,) . replace x y) `fmap` checkWeakening x t n (n' z))
    checkWeakening x t n p
         | t == Lift InTerm && x `notElem` fv n = emptyIn x p
         | otherwise = p
    replace x y t = t'
      where Right t' = CP.runM (CP.replace x y t)
xTerm (EmptyCase m xs t) =
  do (mty@(Lift (Choice [])), m') <- xTerm m
     return (t, \z -> nu (V "x") (xType mty)
                         (m' =<< reference (V "x"))
                         (emptyCase (V "x") xs))
xTerm (Fork x a m) =
  do (mty@(Lift OutTerm), m') <- provide x (Lift a) (xTerm m)
     return (Lift (dual a),
             \z -> nu x (xSession (dual a))
                      (nu (V "y") CP.Bottom (m' =<< reference (V "y")) (emptyOut (V "y")))
                      (link x z))
xTerm (Serve x a m) =
  do (t@(Lift OutTerm), m') <- provide x (Lift a) (xTerm m)
     return (Lift (dual a),
             \z -> nu x (xSession (dual a))
                      (nu (V "y") CP.Bottom (m' =<< reference (V "y")) (emptyOut (V "y")))
                      (link x z))
xTerm (Request m) =
  do (t@(Lift (Service ty)), m') <- xTerm m
     return (Lift ty,
             \z -> nu (V "x") (CP.OfCourse (xSession ty))
                      (m' =<< reference (V "x"))
                      (derelict (V "x") (V "y") (link (V "y") z)))
xTerm (SendType s m) =
  do (mty@(Lift (OutputType v s')), m') <- xTerm m
     return (Lift (instSession v s s'),
             \z -> nu (V "x") (CP.dual (xType mty))
                      (sendType (V "x") (xSession s) (link (V "x") z))
                      (m' =<< reference (V "x")))
xTerm (ReceiveType m) =
  do (mty@(Lift (InputType v s')), m') <- xTerm m
     return (Lift s',
             \z -> nu (V "x") (CP.dual (xType mty))
                      (receiveType (V "x") v (link (V "x") z))
                      (m' =<< reference (V "x")))
