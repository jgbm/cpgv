module Expand where

import Check (Behavior, dual)
import Control.Monad
import Control.Monad.Error
import Syntax.AbsCP
import Syntax.PrintCP

data Defns = D { procs :: [(UIdent, ([ProcParam], Proc))],
                 names :: [(LIdent, LIdent)],
                 types :: [(UIdent, ([UIdent], Type))] }

emptyDefns = D [] [] []

getBinding :: (Eq k, Print k) => k -> [(k, v)] -> Either String v
getBinding k ds = case lookup k ds of
                    Nothing -> Left ("Unable to find definition of " ++ printTree k)
                    Just v  -> Right v

addDefn :: Defns -> Defn -> Defns
addDefn ds (DefnNoArgs id p)      = ds{ procs = (id, ([], p)) : procs ds }
addDefn ds (DefnArgs id vs p)     = ds{ procs = (id, (vs, p)) : procs ds }
addDefn ds (TypeDefnNoArgs id t)  = ds{ types = (id, ([], t)) : types ds }
addDefn ds (TypeDefnArgs id vs t) = ds{ types = (id, (vs, t)) : types ds }

addNameBinding :: Defns -> LIdent -> LIdent -> Defns
addNameBinding ds x y = ds{ names = (x, y) : names ds }

filterTypeDefns :: (UIdent -> Bool) -> Defns -> Defns
filterTypeDefns p ds = ds{ types = filter (p . fst) (types ds) }

filterNameBindings :: (LIdent -> Bool) -> Defns -> Defns
filterNameBindings p ds = ds{ names = filter (p . fst) (names ds) }

expandP :: Defns -> Proc -> Either String Proc
expandP ds = ex
    where ex (ProcVar v)           = do (vs, p) <- getBinding v (procs ds)
                                        if null vs
                                        then return p
                                        else throwError ("Wrong number of arguments for " ++ printTree v)
          ex (ProcVarArgs v ps)    = do (vs, p) <- getBinding v (procs ds)
                                        if length vs == length ps
                                        then let addBinding ds (ProcParam v, ProcArg p) = return (addDefn ds (DefnNoArgs v p))
                                                 addBinding ds (NameParam x, NameArg y) = return (addNameBinding ds x y)
                                                 addBinding _ _ = throwError "Argument class does not match parameter class"
                                             in  do ds' <- foldM addBinding ds (zip vs ps)
                                                    expandP ds' p
                                        else throwError ("Wrong number of arguments for " ++ printTree v)
          ex (Link w x)            = return (Link (exn w) (exn x))
          ex (Comp x a p q)        = liftM3 (Comp (exn x)) (expandT ds a) (expandP (filterNameBindings (x /=) ds) p)
                                                                          (expandP (filterNameBindings (x /=) ds) q)
          ex (Out x y p q)         = liftM2 (Out (exn x) y) (expandP (filterNameBindings (y /=) ds) p)
                                                            (ex q)
          ex (In x y p)            = liftM (In (exn x) y) (expandP (filterNameBindings (y /=) ds) p)
          ex (Inj x l p)           = liftM (Inj (exn x) l) (ex p)
          ex (Case x bs)           = liftM (Case (exn x)) (sequence [Branch l `fmap` ex p | Branch l p <- bs])
          ex (ServerAccept x y p)  = liftM (ServerAccept (exn x) y) (expandP (filterNameBindings (y /=) ds) p)
          ex (ClientRequest x y p) = liftM (ClientRequest (exn x) y) (expandP (filterNameBindings (y /=) ds) p)
          ex (SendType x a p)      = liftM2 (SendType (exn x)) (expandT ds a) (ex p)
          ex (ReceiveType x a p)   = liftM (ReceiveType (exn x) a) (expandP (filterTypeDefns (a /=) ds) p)
          ex (EmptyOut x)          = return (EmptyOut (exn x))
          ex (EmptyIn x p)         = liftM (EmptyIn (exn x)) (ex p)
          ex (EmptyCase x ys)      = return (EmptyCase (exn x) (map exn ys))

          exn x = case getBinding x (names ds) of
                    Left _  -> x
                    Right y -> y

expandT :: Defns -> Type -> Either String Type
expandT ds (Exists x t)   = liftM (Exists x) (expandT (filterTypeDefns (x /=) ds) t)
expandT ds (ForAll x t)   = liftM (ForAll x) (expandT (filterTypeDefns (x /=) ds) t)
expandT ds (Times t u)    = liftM2 Times (expandT ds t) (expandT ds u)
expandT ds (Par t u)      = liftM2 Par (expandT ds t) (expandT ds u)
expandT ds (Plus lts)     = liftM Plus (sequence [Label l `fmap` expandT ds t | Label l t <- lts])
expandT ds (With lts)     = liftM With (sequence [Label l `fmap` expandT ds t | Label l t <- lts])
expandT ds (OfCourse t)   = liftM OfCourse (expandT ds t)
expandT ds (WhyNot t)     = liftM WhyNot (expandT ds t)
expandT ds (Var v)        = case getBinding v (types ds) of
                              Left _ -> return (Var v)
                              Right ([], t) -> expandT ds t
                              Right _  -> throwError ("Wrong number of arguments for " ++ printTree v)
expandT ds (VarArgs v ts) = do (vs, t) <- getBinding v (types ds)
                               if length vs == length ts
                               then let ds' = foldr (\(v,t) ds -> addDefn ds (TypeDefnNoArgs v t)) ds (zip vs ts)
                                    in  expandT ds' t
                               else throwError ("Wrong number of arguments for " ++ printTree v)
expandT ds (Dual t)       = liftM dual (expandT ds t)
expandT ds One            = return One
expandT ds Bottom         = return Bottom
-- expandT ds Zero           = return Zero
-- expandT ds Top            = return Top

expandB :: Defns -> Behavior -> Either String Behavior
expandB ds b = sequence [liftM (Typing v) (expandT ds t) | Typing v t <- b]
