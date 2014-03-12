{-# LANGUAGE TupleSections, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
module CP.Expand where

import Control.Monad
import Control.Monad.Error
import Data.List
import CP.Syntax
import CP.Printer

expandA :: Defns -> Arg -> M Arg
expandA ds (NameArg v) = case lookup v (names ds) of
                          Nothing -> return (NameArg v)
                          Just v' -> return (NameArg v')
expandA ds (ProcArg p) = ProcArg `fmap` expandP ds p

expandP :: Defns -> Proc -> M Proc
expandP ds = ex
    where ex (ProcVar v ps)    = do (vs, p) <- getBinding' v (procs ds)
                                    ps' <- mapM (expandA ds) ps
                                    if length vs == length ps
                                    then let addBinding ds (ProcParam v, ProcArg p) = return (addDefn ds (ProcDef v [] p))
                                             addBinding ds (NameParam x, NameArg y) = return (addNameBinding ds x y)
                                             addBinding _ _ = throwError "Argument class does not match parameter class"
                                             showCP x = displayS (renderPretty 0.8 120 (pretty x)) ""
                                         in  do ds' <- foldM addBinding ds (zip vs ps')
                                                expandP ds' p
                                    else throwError ("Wrong number of arguments for " ++ v)
          ex (Link w x)            = return (Link (exn w) (exn x))
          ex (Cut x a p q) = do x' <- fresh x
                                let ds' = addNameBinding ds x x'
                                liftM3 (Cut x') (expandT ds a) (expandP ds' p) (expandP ds' q)
          ex (Out x y p q) = do y' <- fresh y
                                let ds' = addNameBinding ds y y'
                                liftM2 (Out (exn x) y') (expandP ds' p) (ex q)
          ex (In x y p) = do y' <- fresh y
                             let ds' = addNameBinding ds y y'
                             liftM (In (exn x) y') (expandP ds' p)
          ex (Select x l p)        = liftM (Select (exn x) l) (ex p)
          ex (Case x bs)           = liftM (Case (exn x)) (sequence [(l,) `fmap` ex p | (l, p) <- bs])
          ex (Unroll x p)          = liftM (Unroll (exn x)) (ex p)
          ex (Roll x y a p q)      = do y' <- fresh y
                                        let ds' = addNameBinding ds y y'
                                        liftM3 (Roll (exn x) y') (expandT ds a) (expandP ds' p) (expandP ds' q)
          ex (Replicate x y p)     = liftM (Replicate (exn x) y) (expandP (filterNameBindings (y /=) ds) p)
          ex (Derelict x y p)      = liftM (Derelict (exn x) y) (expandP (filterNameBindings (y /=) ds) p)
          ex (SendProp x a p)      = liftM2 (SendProp (exn x)) (expandT ds a) (ex p)
          ex (ReceiveProp x a p)   = liftM (ReceiveProp (exn x) a) (expandP (filterTypeDefns (a /=) ds) p)
          ex (SendTerm x m p)      = liftM (SendTerm (exn x) m) (ex p)
          ex (ReceiveTerm x i p)   = liftM (ReceiveTerm (exn x) i) (ex p)
          ex (EmptyOut x)          = return (EmptyOut (exn x))
          ex (EmptyIn x p)         = liftM (EmptyIn (exn x)) (ex p)
          ex (EmptyCase x ys)      = return (EmptyCase (exn x) (map exn ys))
          ex (Quote m _)           = return (Quote m (Just ds{ names = units ++ names' }))
              where cs = channels m
                    names' = filter ((`elem` cs) . fst) (names ds)
                    units  = [(x, x) | x <- cs, x `notElem` map fst names']
          ex (Unk ys)              = return (Unk (map exn ys))

          exn x = case getBinding x (names ds) of
                    Left _ -> x
                    Right y -> y

expandBinder ds f x t = liftM (f x) (expandT (filterTypeDefns (x /=) ds) t)

expandT :: Defns -> Prop -> M Prop
expandT ds (Exist x t)    = expandBinder ds Exist x t
expandT ds (Univ x t)     = expandBinder ds Univ x t
expandT ds (Mu x t)       = expandBinder ds Mu x t
expandT ds (Nu x t)       = expandBinder ds Nu x t
expandT ds (Times t u)    = liftM2 Times (expandT ds t) (expandT ds u)
expandT ds (Par t u)      = liftM2 Par (expandT ds t) (expandT ds u)
expandT ds (Plus lts)     = liftM Plus (sequence [(l,) `fmap` expandT ds t | (l, t) <- lts])
expandT ds (With lts)     = liftM With (sequence [(l,) `fmap` expandT ds t | (l, t) <- lts])
expandT ds (OfCourse t)   = liftM OfCourse (expandT ds t)
expandT ds (WhyNot t)     = liftM WhyNot (expandT ds t)
expandT ds (Neg v)        = case getBinding v (types ds) of
                              Left _ -> return (Neg v)
                              Right ([], t) -> expandT (filterTypeDefns (v /=) ds) (dual t)
                              Right _  -> throwError ("Wrong number of arguments for " ++ v)
expandT ds (Var v ts) = case getBinding v (types ds) of
                          Left err | null ts -> return (Var v [])
                                   | otherwise -> throwError err
                          Right (vs, t) ->
                              do ts' <- mapM (expandT ds) ts
                                 if length vs == length ts
                                 then let ds' = foldr (\(v,t) ds -> addDefn ds (PropDef v [] t))
                                                      (filterTypeDefns (v /=) ds)
                                                      (zip vs ts')
                                      in  expandT ds' t
                                 else throwError ("Wrong number of arguments for " ++ v)
expandT ds (FOUniv t a)   = liftM (FOUniv t) (expandT ds a)
expandT ds (FOExist t a)  = liftM (FOExist t) (expandT ds a)
expandT ds (Dual t)       = liftM dual (expandT ds t)
expandT ds One            = return One
expandT ds Bottom         = return Bottom

expandB :: Defns -> Behavior -> M Behavior
expandB ds b = sequence [liftM (exn v,) (expandT ds t) | (v, t) <- b]
    where exn x = case getBinding x (names ds) of
                    Left _ -> x
                    Right y -> y

expandTop :: Defns -> Proc -> Behavior -> M (Proc, Behavior)
expandTop ds p b = do vs' <- mapM fresh vs
                      let ds' = foldl (\ds (x, y) -> addNameBinding ds x y) ds (zip vs vs')
                      p'  <- expandP ds' p
                      b'  <- expandB ds' b
                      return (p', b')
    where vs = map fst b
