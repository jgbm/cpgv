{-# LANGUAGE PatternGuards, TupleSections #-}
module GV.Check where

import Prelude hiding (replicate)

import Control.Monad.Error
import Data.List hiding (replicate)
import GV.Syntax
import GV.Printer

import GV.CPBuilder
import qualified CP.Check as CP (dual)
import qualified CP.Syntax as CP


--------------------------------------------------------------------------------
-- Types, substitutions, and unifications

dual :: Session -> Session
dual (Dual st)    = st
dual (Output t s) = Input t (dual s)
dual (Input t s)  = Output t (dual s)
dual (Sum cs)     = Choice [(l, dual s) | (l, s) <- cs]
dual (Choice cs)  = Sum [(l, dual s) | (l, s) <- cs]
dual InTerm       = OutTerm
dual OutTerm      = InTerm
dual (Server s)   = Service (dual s)
dual (Service s)  = Server (dual s)
dual (SVar x)     = Neg x
dual (Neg x)      = SVar x
dual (OutputType x s) = InputType x (dual s)
dual (InputType x s)  = OutputType x (dual s)


linear :: Type -> Bool
linear (LinFun _ _)       = True
linear (Tensor _ _)       = True
linear (Lift (Service _)) = False
linear (Lift _)           = True
linear _                  = False

unlimited :: Type -> Bool
unlimited = not . linear



--------------------------------------------------------------------------------
-- Free session variables
fsv :: Session -> [String]
fsv (Output t s) = ftv t ++ fsv s
fsv (Input t s) = ftv t ++ fsv s
fsv (Sum ls) = concatMap (fsv . snd) ls
fsv (Choice ls) = concatMap (fsv . snd) ls
fsv OutTerm = []
fsv InTerm = []
fsv (Server s) = fsv s
fsv (Service s) = fsv s
fsv (SVar x) = [x]
fsv (Neg x) = [x]
fsv (OutputType x s) = filter (x /=) (fsv s)
fsv (InputType x s) = filter (x /=) (fsv s)

ftv :: Type -> [String]
ftv (LinFun t u) = ftv t ++ ftv u
ftv (UnlFun t u) = ftv t ++ ftv u
ftv (Tensor t u) = ftv t ++ ftv u
ftv (Lift s) = fsv s
ftv UnitType = []

--------------------------------------------------------------------------------
-- Instantiating session variables
instSession :: String -> Session -> Session -> Session
instSession x s (Output t s') = Output (instType x s t) (instSession x s s')
instSession x s (Input t s') = Input (instType x s t) (instSession x s s')
instSession x s (Sum lts) = Sum [(l, instSession x s s') | (l, s') <- lts]
instSession x s (Choice lts) = Choice [(l, instSession x s s') | (l, s') <- lts]
instSession x s OutTerm = OutTerm
instSession x s InTerm = InTerm
instSession x s (Server s') = Server (instSession x s s')
instSession x s (Service s') = Service (instSession x s s')
instSession x s (SVar y) | x == y = s
                         | otherwise = SVar y
instSession x s (Dual s') = dual (instSession x s s')
instSession x s (Neg y) | x == y = s
                        | otherwise = Neg y
instSession x s (OutputType y s') | x == y = OutputType y s'
                                  | otherwise = OutputType y (instSession x s s')
instSession x s (InputType y s') | x == y = InputType y s'
                                  | otherwise = InputType y (instSession x s s')

instType :: String -> Session -> Type -> Type
instType x s (LinFun t u) = LinFun (instType x s t) (instType x s u)
instType x s (UnlFun t u) = LinFun (instType x s t) (instType x s u)
instType x s (Tensor t u) = LinFun (instType x s t) (instType x s u)
instType x s (Lift s') = Lift (instSession x s s')
instType x s UnitType = UnitType

--------------------------------------------------------------------------------
-- Typechecking monad and non-proper morphisms

type Typing = (String, Type)
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
typeFrom = snd

nameFrom :: Typing -> String
nameFrom = fst

checkLinear :: Check ()
checkLinear = C (\e -> case filter (linear . typeFrom) e of
                         [] -> Right ((), e)
                         e' -> Left ("    Failed to consume bindings for " ++ intercalate "," (map nameFrom e')))

-- Limits the environment to only those typings satisfying the given predicate;
-- excluded bindings and restored after the subcomputation is evaluated.
restrict :: (Typing -> Bool) -> Check t -> Check t
restrict p c = C (\e -> let (eIn, eOut) = partition p e
                        in  case runCheck c eIn of
                              Left err -> Left err
                              Right (v, eIn') -> Right (v, eIn' ++ eOut))

-- Find the type of a variable; if its type is linear, remove it from the
-- environment.
consume :: String -> Check Type
consume x = C (\e -> case partition ((x ==) . nameFrom) e of
                       ([], _)            -> Left ("    Failed to find binding for " ++ x)
                       ([(_, t)], e')
                           | unlimited t  -> Right (t, e)
                           | otherwise    -> Right (t, e')
                       _                  -> error ("Multiple bindings for " ++ x))

-- Add a new binding to the environment; if its type is linear, assure that it
-- is consumed in the provided subcomputation.  If this shadows an existing
-- binding, the existing binding is restored after the subcomputation finishes.
provide :: String -> Type -> Check t -> Check t
provide x t c = C (\e -> let (included, excluded) = partition ((x /=) . nameFrom) e
                         in  case runCheck c ((x, t) : included) of
                               Left err -> Left err
                               Right (y, e')
                                   | unlimited t -> Right (y, excluded ++ filter ((x /=) . nameFrom) e')
                                   | otherwise   -> case partition ((x ==) . nameFrom) e' of
                                                      ([], _) -> Right (y, excluded ++ e')
                                                      _       -> Left ("    Failed to consume binding for " ++ x))

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
          filterUnlimited = filter (linear . snd)
          domain = map nameFrom
          equalAsSet xs ys = all (`elem` xs) ys && all (`elem` ys) xs
          getBinding x b = case partition ((x ==) . nameFrom) b of
                             ([(_, t)], _) -> t
                             _                 -> error "getBinding"
          same b b' = equalAsSet (domain b) (domain b') && and [getBinding x b == getBinding x b' | x <- domain b]

addErrorContext :: String -> Check t -> Check t
addErrorContext s c = C (\e -> case runCheck c e of
                                 Left err -> Left (s ++ '\n' : err)
                                 Right r  -> Right r)

--------------------------------------------------------------------------------
-- Translating types

xSession :: Session -> CP.Prop
xSession (Output t s) = CP.dual (xType t) `CP.Par` xSession s
xSession (Input t s)  = xType t `CP.Times` xSession s
xSession (Sum cs)     = CP.With [(l, xSession st) | (l, st) <- cs]
xSession (Choice cs)  = CP.Plus [(l, xSession st) | (l, st) <- cs]
xSession OutTerm      = CP.Bottom
xSession InTerm       = CP.One
xSession (Server s)   = CP.WhyNot (xSession s)
xSession (Service s)  = CP.OfCourse (xSession s)
xSession (SVar s)     = CP.Var s []


xType :: Type -> CP.Prop
xType (Lift s)     = xSession s
xType (LinFun t u) = CP.dual (xType t) `CP.Par` xType u
xType (UnlFun t u) = CP.OfCourse (xType (LinFun t u))
xType (Tensor t u) = xType t `CP.Times` xType u
xType UnitType     = CP.OfCourse (CP.With [])

--------------------------------------------------------------------------------
-- With all that out of the way, type checking itself can be implemented
-- directly.

check :: Term -> Check (Type, String -> Builder CP.Proc)
check te = addErrorContext ("Checking \"" ++ show (pretty te) ++ "\"") (check' te)
    where check' :: Term -> Check (Type, String -> Builder CP.Proc)
          check' (Var x)   = do ty <- consume x
                                return (ty, \z -> link x z)
          check' Unit      = return (UnitType, \z -> replicate z "y" (emptyCase "y" []))
          check' (Link m n) =
              do (t, m') <- check m
                 (t', n') <- check n
                 case (t, t') of
                   (Lift s, Lift s')
                       | s == dual s' -> return (Lift OutTerm,
                                                 \z -> nu (V "x") (xSession s)
                                                          (m' =<< reference (V "x"))
                                                          (nu "y" (xSession s')
                                                              (n' =<< reference (V "y"))
                                                              (emptyIn z (link (V "x") (V "y")))))
                       | otherwise -> fail ("    Sessions in link are not dual: " ++ show (pretty s) ++ " and " ++ show (pretty s'))
                   _ -> fail ("    Non-session arguments to link: " ++ show (pretty t) ++ " and " ++ show (pretty t'))
          check' (UnlLam x t m) =
              do (u, m') <- restrict (unlimited . typeFrom) (provide x t (check m))
                 return (UnlFun t t, \z -> replicate z (V "y") (in_ (V "y") x (m' =<< reference (V "y"))))
          check' (LinLam x t m) =
              do (u, m') <- provide x t (check m)
                 return (LinFun t u, \z -> in_ z x (m' z))
          check' (App m n) =
              do (mty, m') <- check m
                 (nty, n') <- check n
                 case mty of
                   v `LinFun` w
                       | v == nty -> return (w, \z -> nu (V "w") (xType mty) (m' =<< reference (V "w")) (out (V "w") (V "x") (n' =<< reference (V "x")) (link (V "w") z)))
                       | otherwise -> fail ("   Argument has type " ++ show (pretty nty) ++ " but expected " ++ show (pretty v))
                   v `UnlFun` w
                       | v == nty -> return (w, \z -> nu (V "y") (xType (v `LinFun` w))
                                                         (nu (V "w") (xType (v `UnlFun` w)) (m' =<< reference (V "w")) (derelict (V "w") (V "x") (link (V "x") (V "y"))))
                                                         (out (V "y") (V "x") (n' =<< reference (V "x")) (link (V "y") z)))
                       | otherwise -> fail ("   Argument has type " ++ show (pretty nty) ++ " but expected " ++ show (pretty v))
                   _ -> fail ("   Application of non-function of type " ++ show (pretty mty))
          check' (Pair m n) =
              do (mty, m') <- check m
                 (nty, n') <- check n
                 return (Tensor mty nty, \z -> out z (V "y") (m' =<< reference (V "y")) (n' z))
          check' (Let (BindName x) m n) =
              do (t, m') <- check m
                 (u, n') <- provide x t (check n)
                 return (u, \z -> nu x (xType t) (m' =<< reference x) (n' z))
          check' (Let BindUnit m n) =
              do (mty, m') <- check m
                 case mty of
                   UnitType -> do (nty, n') <- check n
                                  return (nty, \z -> nu (V "x") (xType mty)
                                                        (m' =<< reference (V "x"))
                                                        (n' z))
                   _        -> fail ("    Attempted to pattern-match non-unit of type " ++ show (pretty mty))
          check' (Let (BindPair x y) m n) =
              do (mty, m') <- check m
                 case mty of
                   Tensor xty yty -> do (nty, n') <- provide x xty (provide y yty (check n))
                                        return (nty, \z -> nu y (xType mty) (m' =<< reference y) (in_ y x (n' z)))
                   _              -> fail ("    Attempted to pattern-match non-pair of type " ++ show (pretty mty))
          check' (Send m n) =
              do (mty, m') <- check m
                 (nty, n') <- check n
                 case nty of
                   Lift (Output v w)
                        | mty == v -> return (Lift w, \z -> nu (V "x") (xType v `CP.Times` CP.dual (xSession w))
                                                                   (out (V "x") (V "y") (m' =<< reference (V "y")) (link (V "x") z)) (n' =<< reference (V "x")))
                        | otherwise -> fail ("    Sent value has type " ++ show (pretty mty) ++ " but expected " ++ show (pretty v))
                   _ -> fail ("    Channel of send operation has unexpected type " ++ show (pretty nty))
          check' (Receive m) =
              do (mty, m') <- check m
                 case mty of
                   Lift (Input v w) -> return (v `Tensor` Lift w, m')
                   _ -> fail ("    Channel of receive operation has unexpected type " ++ show (pretty mty))
          check' (Select l m) =
              do (mty, m') <- check m
                 case mty of
                   Lift (Sum cs) -> do st <- lookupLabel l cs
                                       return (Lift st, \z -> nu (V "x") (xType mty) (m' =<< reference (V "x")) (inj (V "x") l (link (V "x") z)))
                   _             -> fail ("    Channel of select operation has unexepcted type " ++ show (pretty mty))
              where
          check' (Case m bs@(_:_))
              | Just l <- duplicated bs = fail ("    Duplicated case label " ++ show (pretty l))
              | otherwise = do (mty, m') <- check m
                               case mty of
                                 Lift (Choice cs) -> do (t:ts, bs') <- unzip `fmap` mapPar (checkBranch cs) bs
                                                        if all (t ==) ts
                                                        then return (t, \z -> nu (V "x") (xType mty)
                                                                                     (m' =<< reference (V "x"))
                                                                                     (case_ (V "x") (sequence [reference (V "x") >>= flip b' z | b' <- bs'])))
                                                        else fail ("   Divergent results of case branches:" ++ intercalate ", " (map (show . pretty) (nub (t:ts))))
                                 _                -> fail ("    Channel of case operation has unexpected type " ++ show (pretty mty))
              where duplicated [] = Nothing
                    duplicated ((l, _, _) : bs)
                        | or [l == l' | (l', _, _) <- bs] = Just l
                        | otherwise = duplicated bs
                    checkBranch :: [(String, Session)] -> (String, String, Term) -> Check (Type, String -> String -> Builder (String, CP.Proc))
                    checkBranch cs (l, x, n) =
                        do s <- lookupLabel l cs
                           provide x (Lift s) (do (t, n') <- check n
                                                  return (t, \y z -> ((l,) . replace x y) `fmap` n' z))
                    replace x y t = t'
                        where Right t' = CP.runM (CP.replace x y t)

          check' (EmptyCase m xs t) =
             do (mty, m') <- check m
                case mty of
                  Lift (Choice []) -> do mapM_ consume xs
                                         return (t, \z -> nu (V "x") (xType mty)
                                                                 (m' =<< reference (V "x"))
                                                                 (emptyCase (V "x") xs))
                  _                -> fail ("    Channel of empty case operation has unexpected type " ++ show (pretty mty))
          check' (With l st m n) =
              do (mty, m') <- provide l (Lift st) (check m)
                 case mty of
                   Lift OutTerm -> do (nty, n') <- provide l (Lift (dual st)) (check n)
                                      return (nty, \z -> nu l (CP.dual (xSession st))
                                                            (nu (V "y") CP.Bottom (m' =<< reference (V "y")) (emptyOut (V "y")))
                                                            (n' z))
                   _            -> fail ("    Unexpected type of left channel " ++ show (pretty mty))
          check' (End m) =
              do (mty, m') <- check m
                 case mty of
                   Lift InTerm -> return (UnitType, \z -> nu (V "x") CP.One
                                                             (m' =<< reference (V "x"))
                                                             (emptyIn (V "x") (replicate z (V "y") (emptyCase (V "y") []))))
                   _           -> fail ("    Unexpected type of terminated channel " ++ show (pretty mty))
          check' (Serve s x m) =
              do sty <- consume s
                 case sty of
                   Lift (Server ty) ->
                     do (u', m') <- provide x (Lift ty) (check m)
                        return (Lift OutTerm, \z ->
                                     emptyIn z
                                       (replicate s x
                                          (nu (V "y") CP.One (emptyOut (V "y"))
                                              (m' =<< reference (V "y")))))
                   _                -> fail ("    Unexpected type of server channel " ++ show (pretty sty))
          check' (Request s) =
              do sty <- consume s
                 case sty of
                   Lift (Service ty) ->
                     return (Lift ty, \z -> derelict s (V "x") (link (V "x") z))
                   _                 -> fail("    Unexpected type of service channel " ++ show (pretty sty))
          check' (SendType s m) =
              do (mty, m') <- check m
                 case mty of
                   Lift (InputType v s') ->
                        return (Lift (instSession v s s'),
                                \z -> nu (V "x") (CP.dual (xType mty))
                                          (sendType (V "x") (xSession s) (link (V "x") z))
                                          (m' =<< reference (V "x")))
                   _ -> fail ("    Channel of send type operation has unexpected type " ++ show (pretty mty))
          check' (ReceiveType m) =
              do (mty, m') <- check m
                 case mty of
                   Lift (OutputType v s') ->
                        return (Lift s',
                                \z -> nu (V "x") (CP.dual (xType mty))
                                          (receiveType (V "x") v (link (V "x") z))
                                          (m' =<< reference (V "x")))
                   _ -> fail ("    Channel of receive type operation has unexpected type " ++ show (pretty mty))


-- [[send S M]](z : !V.S') = nu x.(x[ [[S]] ].[[M]]x | link x z)
-- [[receive M]](z : ?V.S) = nu x.(x(V).[[M]]x | link x z)

--           check' (Send m n) =
--               do (mty, m') <- check m
--                  (nty, n') <- check n
--                  case nty of
--                    Lift (Output v w)
--                         | mty == v -> return (Lift w, \z -> nu (V "x") (xType v `CP.Times` CP.dual (xSession w))
--                                                                    (out (V "x") (V "y") (m' =<< reference (V "y")) (link (V "x") z)) (n' =<< reference (V "x")))
--                         | otherwise -> fail ("    Sent value has type " ++ printTree mty ++ " but expected " ++ printTree v)
--                    _ -> fail ("    Channel of send operation has unexpected type " ++ printTree nty)


lookupLabel :: String -> [(String, Session)] -> Check Session
lookupLabel l [] = fail ("    Unable to find label " ++ l)
lookupLabel l ((l', s) : rest)
    |  l == l'   = return s
    | otherwise  = lookupLabel l rest

checkAgainst :: Term -> Type -> Check (Builder CP.Proc)
checkAgainst te ty = do (ty', b) <- check te
                        if ty == ty'
                        then return (binder (V "z") b)
                        else fail ("Expected type " ++ show (pretty ty) ++ " but actual type is " ++ show (pretty ty'))
