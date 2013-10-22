{-# LANGUAGE PatternGuards #-}
module CheckGV where

import Control.Monad.Error
import Data.List
import Syntax.AbsGV
import Syntax.PrintGV

import CPBuilder
import qualified Check as CP (dual)
import qualified Norm as CP (replace)
import qualified Syntax.AbsCP as CP


--------------------------------------------------------------------------------
-- Types, substitutions, and unifications

dual :: Session -> Session
dual (Dual st)    = st
dual (SVar v)     = Dual (SVar v)
dual (Output t s) = Input t (dual s)
dual (Input t s)  = Output t (dual s)
dual (Sum cs)     = Choice [Label l (dual s) | Label l s <- cs]
dual (Choice cs)  = Sum [Label l (dual s) | Label l s <- cs]
dual InTerm       = OutTerm
dual OutTerm      = InTerm

linear :: Type -> Bool
linear (LinFun _ _) = True
linear (Tensor _ _) = True
linear (Lift _)     = True
linear _            = False

unlimited :: Type -> Bool
unlimited = not . linear

--------------------------------------------------------------------------------
-- Typechecking monad and non-proper morphisms

type Environment = [Typing]

newtype Check t = C{ runCheck :: Environment -> Either String (t, Environment) }
instance Functor Check
    where fmap f (C g) = C (\e -> case g e of
                                    Left err -> Left err
                                    Right (v, e') -> Right (f v, e'))
instance Monad Check
    where return x = C (\e -> Right (x, e))
          C f >>= g = C (\e -> case f e of
                                 Left err -> Left err
                                 Right (v, e') -> runCheck (g v) e')
          fail s = C (\e -> Left s)

typeFrom :: Typing -> Type
typeFrom (Typing _ t) = t

nameFrom :: Typing -> LIdent
nameFrom (Typing id _) = id

checkLinear :: Check ()
checkLinear = C (\e -> case filter (linear . typeFrom) e of
                         [] -> Right ((), e)
                         e' -> Left ("    Failed to consume bindings for " ++ intercalate "," (map (printTree . nameFrom) e')))

-- Limits the environment to only those typings satisfying the given predicate;
-- excluded bindings and restored after the subcomputation is evaluated.
restrict :: (Typing -> Bool) -> Check t -> Check t
restrict p c = C (\e -> let (eIn, eOut) = partition p e
                        in  case runCheck c eIn of
                              Left err -> Left err
                              Right (v, eIn') -> Right (v, eIn' ++ eOut))

-- Find the type of a variable; if its type is linear, remove it from the
-- environment.
consume :: LIdent -> Check Type
consume x = C (\e -> case partition ((x ==) . nameFrom) e of
                       ([], _)            -> Left ("    Failed to find binding for " ++ printTree x)
                       ([Typing _ t], e')
                           | unlimited t  -> Right (t, e)
                           | otherwise    -> Right (t, e')
                       _                  -> error ("Multiple bindings for " ++ printTree x))

-- Add a new binding to the environment; if its type is linear, assure that it
-- is consumed in the provided subcomputation.  If this shadows an existing
-- binding, the existing binding is restored after the subcomputation finishes.
provide :: LIdent -> Type -> Check t -> Check t
provide x t c = C (\e -> let (included, excluded) = partition ((x /=) . nameFrom) e
                         in  case runCheck c (Typing x t : included) of
                               Left err -> Left err
                               Right (y, e')
                                   | unlimited t -> Right (y, excluded ++ filter ((x /=) . nameFrom) e')
                                   | otherwise   -> case partition ((x ==) . nameFrom) e' of
                                                      ([], _) -> Right (y, excluded ++ e')
                                                      _       -> Left ("    Failed to consume binding for " ++ printTree x))

mapPar :: (t -> Check u) -> [t] -> Check [u]
mapPar f xs =
    C (\e -> case runCheck (unzip `fmap` mapM (withEnvironment e . f) xs) e of
               Left err -> Left err
               Right ((ys, es), e')
                   | all (same (filterUnlimited e')) (map filterUnlimited es) ->  Right (ys, e')
                   | otherwise -> Left ("    Branches make inconsistent demands on linear environment"))
    where withEnvironment e c = C (\_ -> case runCheck c e of
                                           Left err -> Left err
                                           Right (y, e) -> Right ((y, e), e))
          filterUnlimited e = [Typing v t | Typing v t <- e, linear t]
          domain = map nameFrom
          equalAsSet xs ys = all (`elem` xs) ys && all (`elem` ys) xs
          getBinding x b = case partition ((x ==) . nameFrom) b of
                             ([Typing _ t], _) -> t
                             _                 -> error "getBinding"
          same b b' = equalAsSet (domain b) (domain b') && and [getBinding x b == getBinding x b' | x <- domain b]

addErrorContext :: String -> Check t -> Check t
addErrorContext s c = C (\e -> case runCheck c e of
                                 Left err -> Left (s ++ '\n' : err)
                                 Right r  -> Right r)

--------------------------------------------------------------------------------
-- Translating types

xSession :: Session -> CP.Type
xSession (Output t s) = CP.dual (xType t) `CP.Par` xSession s
xSession (Input t s)  = xType t `CP.Times` xSession s
xSession (Sum cs)     = CP.With [CP.Label (xId l) (xSession st) | Label l st <- cs]
xSession (Choice cs)  = CP.Plus [CP.Label (xId l) (xSession st) | Label l st <- cs]
xSession OutTerm      = CP.Bottom
xSession InTerm       = CP.One

xType :: Type -> CP.Type
xType (Lift s)     = xSession s
xType (LinFun t u) = CP.dual (xType t) `CP.Par` xType u
xType (UnlFun t u) = CP.OfCourse (xType (LinFun t u))
xType (Tensor t u) = xType t `CP.Times` xType u
xType UnitType     = CP.OfCourse CP.Top

xId (LIdent s) = CP.LIdent s

--------------------------------------------------------------------------------
-- With all that out of the way, type checking itself can be implemented
-- directly.

check :: Term -> Check (Type, CP.LIdent -> Builder CP.Proc)
check te = addErrorContext ("Checking \"" ++ printTree te ++ "\"") (check' te)
    where check' :: Term -> Check (Type, CP.LIdent -> Builder CP.Proc)
          check' (Var x)   = do ty <- consume x
                                return (ty, \z -> link (xId x) z)
          check' Unit      = return (UnitType, \z -> accept z "y" (emptyCase "y"))
          check' (UnlLam x t m) =
              do (u, m') <- restrict (unlimited . typeFrom) (provide x t (check m))
                 return (UnlFun t t, \z -> accept z "y" (in_ "y" (xId x) (m' =<< reference "y")))
          check' (LinLam x t m) =
              do (u, m') <- provide x t (check m)
                 return (LinFun t u, \z -> in_ z (xId x) (m' z))
          check' (App m n) =
              do (mty, m') <- check m
                 (nty, n') <- check n
                 case mty of
                   v `LinFun` w
                       | v == nty -> return (w, \z -> nu "w" (xType mty) (m' =<< reference "w") (out "w" "x" (n' =<< reference "x") (link "w" z)))
                       | otherwise -> fail ("   Argument has type " ++ printTree nty ++ " but expected " ++ printTree v)
                   v `UnlFun` w
                       | v == nty -> return (w, \z -> nu "y" (xType (v `LinFun` w))
                                                         (nu "w" (xType (v `UnlFun` w)) (m' =<< reference "w") (request "w" "x" (link "x" "y")))
                                                         (out "y" "x" (n' =<< reference "x") (link "y" z)))
                       | otherwise -> fail ("   Argument has type " ++ printTree nty ++ " but expected " ++ printTree v)
                   _ -> fail ("   Application of non-function of type " ++ printTree mty)
          check' (Pair m n) =
              do (mty, m') <- check m
                 (nty, n') <- check n
                 return (Tensor mty nty, \z -> out z "y" (m' =<< reference "y") (n' z))
          check' (Let (BindName x) m n) =
              do (t, m') <- check m
                 (u, n') <- provide x t (check n)
                 return (u, \z -> nu (xId x) (xType t) (m' =<< reference (xId x)) (n' z))
          check' (Let (BindPair x y) m n) =
              do (mty, m') <- check m
                 case mty of
                   Tensor xty yty -> do (nty, n') <- provide x xty (provide y yty (check n))
                                        return (nty, \z -> nu (xId y) (xType mty) (m' =<< reference (xId y)) (in_ (xId y) (xId x) (n' z)))
                   _              -> fail ("    Attempted to pattern-match non-pair of type " ++ printTree mty)
          check' (Send m n) =
              do (mty, m') <- check m
                 (nty, n') <- check n
                 case nty of
                   Lift (Output v w)
                        | mty == v -> return (Lift w, \z -> nu "x" (xType v `CP.Times` CP.dual (xSession w))
                                                                   (out "x" "y" (m' =<< reference "y") (link "x" z)) (n' =<< reference "x"))
                        | otherwise -> fail ("    Sent value has type " ++ printTree mty ++ " but expected " ++ printTree v)
                   _ -> fail ("    Channel of send operation has unexpected type " ++ printTree nty)
          check' (Receive m) =
              do (mty, m') <- check m
                 case mty of
                   Lift (Input v w) -> return (v `Tensor` Lift w, m')
                   _ -> fail ("    Channel of receive operation has unexpected type " ++ printTree mty)
          check' (Select l m) =
              do (mty, m') <- check m
                 case mty of
                   Lift (Sum cs) -> do st <- lookupLabel l cs
                                       return (Lift st, \z -> nu "x" (xType mty) (m' =<< reference "x") (inj "x" (xId l) (link "x" z)))
                   _             -> fail ("    Channel of select operation has unexepcted type " ++ printTree mty)
              where
          check' (Case m bs)
              | Just l <- duplicated bs = fail ("    Duplicated case label " ++ printTree l)
              | otherwise = do (mty, m') <- check m
                               case mty of
                                 Lift (Choice cs) -> do (t:ts, bs') <- unzip `fmap` mapPar (checkBranch cs) bs
                                                        if all (t ==) ts
                                                        then return (t, \z -> nu "x" (xType mty) (m' =<< reference "x") (case_ "x" (sequence [reference "x" >>= flip b' z | b' <- bs'])))
                                                        else fail ("   Divergent results of case branches:" ++ intercalate ", " (map printTree (nub (t:ts))))
                                 _                -> fail ("    Channel of case operation has unexpected type " ++ printTree mty)
              where duplicated [] = Nothing
                    duplicated (Branch l _ _ : bs)
                        | or [l == l' | Branch l' _ _ <- bs] = Just l
                        | otherwise = duplicated bs
                    checkBranch cs (Branch l x n) =
                        do s <- lookupLabel l cs
                           provide x (Lift s) (do (t, n') <- check n
                                                  return (t, \y z -> (CP.Branch (xId l) . CP.replace (xId x) y) `fmap` n' z))
          check' (With l st m n) =
              do (mty, m') <- provide l (Lift st) (check m)
                 case mty of
                   Lift OutTerm -> do (nty, n') <- provide l (Lift (dual st)) (check n)
                                      return (nty, \z -> nu (xId l) (CP.dual (xSession st))
                                                            (nu "y" CP.Bottom (m' =<< reference "y") (emptyOut "y"))
                                                            (n' z))
                   _            -> fail ("    Unexpected type of left channel " ++ printTree mty)
          check' (End m) =
              do (mty, m') <- check m
                 case mty of
                   ty `Tensor` Lift InTerm -> return (ty, \z -> nu "y" (xType ty `CP.Times` CP.One)
                                                                   (m' =<< reference "y")
                                                                   (in_ "y" "x" (emptyIn "y" (link "x" z))))
                   _                       -> fail ("    Unexpected type of right channel " ++ printTree mty)


lookupLabel :: LIdent -> [LabeledSession] -> Check Session
lookupLabel l [] = fail ("    Unable to find label " ++ printTree l)
lookupLabel l (Label l' s : rest)
    |  l == l'   = return s
    | otherwise  = lookupLabel l rest

checkAgainst :: Term -> Type -> Check (Builder CP.Proc)
checkAgainst te ty = do (ty', b) <- check te
                        if ty == ty'
                        then return (binder "z" b)
                        else fail ("Expected type " ++ printTree ty ++ " but actual type is " ++ printTree ty')