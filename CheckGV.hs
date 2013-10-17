{-# LANGUAGE PatternGuards #-}
module CheckGV where

import Control.Monad.Error
import Data.List
import Syntax.AbsGV
import Syntax.PrintGV

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

type Subst = ([(LIdent, Type)], [(LIdent, Session)])

printSubst (ts, sts) = "{" ++ intercalate ", " ([printTree v ++ " :-> " ++ printTree t | (v, t) <- ts] ++ [printTree v ++ " :-> " ++ printTree st | (v, st) <- sts]) ++ "}"

(ts, ss) `compose` (ts', ss') = (ts ++ ts', ss ++ ss')
empty = ([], [])
singletonT v t = ([(v, t)], [])
singletonS v st = ([], [(v, st)])

apply :: Subst -> Type -> Type
apply s (TVar v) =
    case lookup v (fst s) of
      Just t -> apply s t
      _      -> TVar v
apply s (LinFun t u) = LinFun (apply s t) (apply s u)
apply s (UnlFun t u) = UnlFun (apply s t) (apply s u)
apply s (Tensor t u) = Tensor (apply s t) (apply s u)
apply s (Lift st)    = Lift (applyS s st)
apply s UnitType     = UnitType

applyS :: Subst -> Session -> Session
applyS s (SVar v)      = case lookup v (snd s) of
                           Just st -> applyS s st
                           _       -> SVar v
applyS s (Dual (SVar v)) = case lookup v (snd s) of
                             Just st -> applyS s (dual st)
                             _       -> Dual (SVar v)
applyS s (Dual st)     = applyS s (dual st)
applyS s (Output t st) = Output (apply s t) (applyS s st)
applyS s (Input t st)  = Input (apply s t) (applyS s st)
applyS s (Sum cs)      = Sum [Label v (applyS s st) | Label v st <- cs]
applyS s (Choice cs)   = Choice [Label v (applyS s st) | Label v st <- cs]
applyS s OutTerm       = OutTerm
applyS s InTerm        = InTerm

unifyTwo :: Type -> Type -> Type -> Type -> Either String Subst
unifyTwo t u t' u' =
    do s <- unify t t'
       (`compose` s) `fmap` unify (apply s u) (apply s u')

unify :: Type -> Type -> Either String Subst
unify (TVar v) (TVar w) | v == w = return empty
unify (TVar v) t = return (singletonT v t)
unify t (TVar v) = return (singletonT v t)
unify (LinFun t u) (LinFun t' u') = unifyTwo t u t' u'
unify (UnlFun t u) (UnlFun t' u') = unifyTwo t u t' u'
unify (Tensor t u) (Tensor t' u') = unifyTwo t u t' u'
unify (Lift st) (Lift st') = unifyS st st'
    where unifyS (SVar v) (SVar w) | v == w = return empty
          unifyS (SVar v) st = return (singletonS v st)
          unifyS st (SVar v) = return (singletonS v st)
          unifyS (Dual (SVar v)) st = return (singletonS v (dual st))
          unifyS st (Dual (SVar v)) = return (singletonS v (dual st))
          unifyS (Dual st) st' = unifyS (dual st) st'
          unifyS st (Dual st') = unifyS st (dual st')
          unifyS (Output t st) (Output t' st') =
              do s <- unify t t'
                 (`compose` s) `fmap` unifyS (applyS s st) (applyS s st')
          unifyS (Input t st) (Input t' st') =
              do s <- unify t t'
                 (`compose` s) `fmap` unifyS (applyS s st) (applyS s st')
          unifyS (Sum cs) (Sum cs') = unifyList cs cs'
          unifyS (Choice cs) (Choice cs') = unifyList cs cs'
          unifyS OutTerm OutTerm = return empty
          unifyS InTerm InTerm = return empty
          unifyS st st' = throwError ("Unable to unify session types (" ++ printTree st ++ ") and (" ++ printTree st' ++ ")")

          labelFrom (Label l st) = l
          stFrom (Label l st) = st
          apply' s (Label l st) = Label l (applyS s st)

          -- Unification of lists as maps---that is, the two lists do not have
          -- to be in the same order, but they must contain the same labels.
          unifyList :: [LabeledSession] -> [LabeledSession] -> Either String Subst
          unifyList [] [] = return empty
          unifyList [] (y:ys) = throwError ("Missing entry with label " ++ printTree (labelFrom y))
          unifyList (x:xs) ys
              | ([y], ys') <- partition ((labelFrom x ==) . labelFrom) ys =
                  do s <- unifyS (stFrom x) (stFrom y)
                     (`compose` s) `fmap` unifyList (map (apply' s) xs) (map (apply' s) ys')
              | otherwise =
                  throwError ("Missing entry with label " ++ printTree (labelFrom x))
unify UnitType UnitType = return empty
unify t u = throwError ("Unable to unify types (" ++ printTree t ++ ") and (" ++ printTree u ++ ")")

--------------------------------------------------------------------------------
-- Typechecking monad and non-proper morphisms

type Environment = [Typing]

newtype Check t = C{ runCheck :: (Subst, Environment, Int) -> Either String (t, (Subst, Environment, Int)) }
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
checkLinear = C (\(s, e, z) -> case filter (linear . typeFrom) e of
                                 [] -> Right ((), (s, e, z))
                                 e' -> Left ("    Failed to consume bindings for " ++ intercalate "," (map (printTree . nameFrom) e')))

-- Limits the environment to only those typings satisfying the given predicate;
-- excluded bindings and restored after the subcomputation is evaluated.
restrict :: (Typing -> Bool) -> Check () -> Check ()
restrict p c = C (\(s, e, z) -> let (eIn, eOut) = partition p e
                                in  case runCheck c (s, eIn, z) of
                                      Left err -> Left err
                                      Right (v, (s', eIn', z')) -> Right (v, (s', eIn' ++ eOut, z')))

-- Find the type of a variable; if its type is linear, remove it from the
-- environment.
consume :: LIdent -> Check Type
consume x = C (\(s, e, z) -> case partition ((x ==) . nameFrom) e of
                               ([], _)            -> Left ("    Failed to find binding for " ++ printTree x)
                               ([Typing _ t], e')
                                   | unlimited t  -> Right (t, (s, e, z))
                                   | otherwise    -> Right (t, (s, e', z))
                               _                  -> error ("Multiple bindings for " ++ printTree x))

-- Add a new binding to the environment; if its type is linear, assure that it
-- is consumed in the provided subcomputation.  If this shadows an existing
-- binding, the existing binding is restored after the subcomputation finishes.
provide :: LIdent -> Type -> Check t -> Check t
provide x t c = C (\(s, e, z) -> let (included, excluded) = partition ((x /=) . nameFrom) e
                                 in  case runCheck c (s, Typing x t : included, z) of
                                       Left err -> Left err
                                       Right (y, (s', e', z'))
                                           | unlimited t -> Right (y, (s', excluded ++ filter ((x /=) . nameFrom) e', z'))
                                           | otherwise   -> case partition ((x ==) . nameFrom) e' of
                                                              ([], _) -> Right (y, (s', excluded ++ e', z'))
                                                              _       -> Left ("    Failed to consume binding for " ++ printTree x))

-- Runs two computations with the same environment, and assures that they make
-- equivalent changes.
andAlso :: Check () -> Check () -> Check ()
andAlso c c' =
    C (\(s, e, z) -> case runCheck c (s, e, z) of
                       Left err -> Left err
                       Right (_, (s', e', z')) ->
                           case runCheck c' (s', e, z') of
                             Left err -> Left err
                             Right (_, (s'', e'', z''))
                                 | same e' e'' -> Right ((), (s'', e'', z''))
                                 | otherwise   -> let leftOver = filter (`notElem` e'') e' ++ filter (`notElem` e') e''
                                                  in  Left (unlines ("    Failed to consume bindings:" :
                                                                     ["        " ++ printTree x ++ ": " ++ printTree t | Typing x t <- leftOver])))
    where domain = map nameFrom
          equalAsSet xs ys = all (`elem` xs) ys && all (`elem` ys) xs
          getBinding x b = case partition ((x ==) . nameFrom) b of
                             ([Typing _ t], _) -> t
                             _                 -> error "getBinding"
          same b b' = equalAsSet (domain b) (domain b') && and [getBinding x b == getBinding x b' | x <- domain b]

-- Succeeds if either computation succeeds
orElse :: Check t -> Check t -> Check t
orElse c c' =
    C (\e -> case runCheck c e of
               Right v -> Right v
               Left _  -> runCheck c' e)

substitute :: Type -> Check Type
substitute t = C (\(s, e, z) -> Right (apply s t, (s, e, z)))

checkUnifies :: Type -> Type -> Check ()
checkUnifies t u = C (\(s, e, z) -> case unify (apply s t) (apply s u) of
                                      Left err -> Left err
                                      Right s' -> Right ((), (s' `compose` s, e, z)))

freshTVar :: String -> Check Type
freshTVar x = C (\(s, e, z) -> Right (TVar (LIdent (x ++ '$' : show z)), (s, e, z + 1)))

freshSVar :: String -> Check Session
freshSVar x = C (\(s, e, z) -> Right (SVar (LIdent (x ++ '$' : show z)), (s, e, z + 1)))


addErrorContext :: String -> Check t -> Check t
addErrorContext s c = C (\e -> case runCheck c e of
                                 Left err -> Left (s ++ '\n' : err)
                                 Right r  -> Right r)

--------------------------------------------------------------------------------
-- With all that out of the way, type checking itself can be implemented
-- directly.

check :: Term -> Type -> Check ()
check te ty = addErrorContext ("Checking \"" ++ printTree te ++ "\"") (check' te)
    where check' (Var x)   = consume x >>= checkUnifies ty
          check' Unit      = checkUnifies ty UnitType
          check' (Fun x m) = checkUnlFun `orElse` checkLinFun
              where checkUnlFun = do v <- freshTVar "v"
                                     w <- freshTVar "w"
                                     checkUnifies ty (UnlFun v w)
                                     restrict (unlimited . typeFrom) (provide x v (check m w))
                    checkLinFun = do v <- freshTVar "v"
                                     w <- freshTVar "w"
                                     checkUnifies ty (LinFun v w)
                                     provide x v (check m w)
          check' (App m n) =
              do v <- freshTVar "v"
                 check m v
                 w <- freshTVar "w"
                 checkUnifies v (w `LinFun` ty) `orElse` checkUnifies v (w `UnlFun` ty)
                 check n w
          check' (Pair m n) =
              do v <- freshTVar "v"
                 w <- freshTVar "w"
                 checkUnifies ty (v `Tensor` w)
                 check m v
                 check n w
          check' (Let (BindName x) m n) =
              do v <- freshTVar "v"
                 check m v
                 provide x v (check n ty)
          check' (Let (BindPair x y) m n) =
              do v <- freshTVar "v"
                 w <- freshTVar "w"
                 check m (v `Tensor` w)
                 provide x v (provide y w (check n ty))
          check' (Send m n) =
              do v <- freshTVar "v"
                 check m v
                 w <- freshSVar "w"
                 check n (Lift (Output v w))
                 checkUnifies ty (Lift w)
          check' (Receive m) =
              do v <- freshTVar "v"
                 w <- freshSVar "w"
                 checkUnifies ty (v `Tensor` (Lift w))
                 check m (Lift (Input v w))
          -- I'm not sure this is right.  In particular, it relies on 'm' having
          -- a type that is at least +{l:S,...}; should the type of 'm' not be
          -- fixed yet, it fails.  However, the only way I can think to
          -- implement the more flexible behavior involves row variables, so I'm
          -- putting that off for now.
          check' (Select l m) =
              do v <- freshTVar "v"
                 check m v
                 sumTy <- substitute v
                 case sumTy of
                   Lift (Sum cs)
                       | Just ty' <- lookupLabel l cs -> checkUnifies ty (Lift ty')
                       | otherwise                    -> fail ("    Missing label " ++ printTree l ++ " in sum " ++ printTree (Sum cs))
                   _                                  -> fail ("    Unexpected type " ++ printTree sumTy)
              where lookupLabel l [] = Nothing
                    lookupLabel l (Label l' s : rest)
                        |  l == l'   = Just s
                        | otherwise  = lookupLabel l rest
          check' (Case m bs)
              | Just l <- duplicated bs = fail ("    Duplicated case label " ++ printTree l)
              | otherwise = do cs <- mapM checkBranch bs
                               check m (Lift (Choice cs))
              where duplicated [] = Nothing
                    duplicated (Branch l _ _ : bs)
                        | or [l == l' | Branch l' _ _ <- bs] = Just l
                        | otherwise = duplicated bs
                    checkBranch (Branch l x te') =
                        do s <- freshSVar "s"
                           provide x (Lift s) (check te' ty)
                           return (Label l s)
          check' (With l m n) =
              do v <- freshSVar "v"
                 provide l (Lift v) (check m (Lift OutTerm))
                 provide l (Lift (Dual v)) (check n ty)
          check' (End m) = check m (ty `Tensor` Lift InTerm)
