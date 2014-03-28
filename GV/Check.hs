{-# LANGUAGE PatternGuards, TupleSections #-}
module GV.Check where

import Prelude hiding (replicate)

import Control.Monad.Error
import Data.List hiding (replicate)
import GV.Syntax
import GV.Printer

import GV.CPBuilder
import qualified CP.Syntax as CP

-------------------------------------------------------------------------------
-- Typechecking monad and non-proper morphisms

type Typing = (String, Type)
type Environment = [Typing]

newtype Check t = C{ runCheck :: (Environment, Int) -> Either String (t, (Environment, Int)) }
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

fresh :: String -> Check String
fresh s = C (\(e, z) -> Right (s ++ '$' : show z, (e, z+ 1)))

checkLinear :: Check ()
checkLinear = C (\(e, z) -> case filter (linear . typeFrom) e of
                              [] -> Right ((), (e, z))
                              e' -> Left ("    Failed to consume bindings for " ++ intercalate "," (map nameFrom e')))

-- Limits the environment to only those typings satisfying the given predicate;
-- excluded bindings and restored after the subcomputation is evaluated.
restrict :: (Typing -> Bool) -> Check t -> Check t
restrict p c = C (\(e, z) -> let (eIn, eOut) = partition p e
                             in  case runCheck c (eIn, z) of
                                   Left err -> Left err
                                   Right (v, (eIn', z')) -> Right (v, (eIn' ++ eOut, z')))

-- Find the type of a variable; if its type is linear, remove it from the
-- environment.
consume :: String -> Check Type
consume x = C (\(e, z) -> case partition ((x ==) . nameFrom) e of
                            ([], _)            -> Left ("    Failed to find binding for " ++ x)
                            ([(_, t)], e')
                                | unlimited t  -> Right (t, (e, z))
                                | otherwise    -> Right (t, (e', z))
                            _                  -> error ("Multiple bindings for " ++ x))

-- Add a new binding to the environment; if its type is linear, assure that it
-- is consumed in the provided subcomputation.  If this shadows an existing
-- binding, the existing binding is restored after the subcomputation finishes.
provide :: String -> Type -> Check t -> Check t
provide x t c = C (\(e, z) -> let (included, excluded) = partition ((x /=) . nameFrom) e
                              in  case runCheck c ((x, t) : included, z) of
                                    Left err -> Left err
                                    Right (y, (e', z'))
                                        | unlimited t -> Right (y, (excluded ++ filter ((x /=) . nameFrom) e', z'))
                                        | otherwise   -> case partition ((x ==) . nameFrom) e' of
                                                           ([], _) -> Right (y, (excluded ++ e', z'))
                                                           _       -> Left ("    Failed to consume binding for " ++ x))

mapPar :: (t -> Check u) -> [t] -> Check [u]
mapPar f xs =
    C (\(e, z) -> case runCheck (unzip `fmap` mapM (withEnvironment e . f) xs) (e, z) of
                    Left err -> Left err
                    Right ((ys, es), (e', z'))
                        | all (same (filterUnlimited e')) (map filterUnlimited es) ->  Right (ys, (e', z'))
                        | otherwise -> Left ("    Branches make inconsistent demands on linear environment"))
    where withEnvironment e c = C (\(_, z) -> case runCheck c (e, z) of
                                                Left err -> Left err
                                                Right (y, (e', z)) -> Right ((y, e'), (e', z)))
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
-- With all that out of the way, type checking itself can be implemented
-- directly.

check :: Term -> Check Type
check te = addErrorContext ("Checking \n" ++ unlines (map ("    " ++) (lines (show (pretty te))))) (check' te)
    where checkUnrolling :: Term -> Check Type
          checkUnrolling (Var x) = do ty <- consume x
                                      case ty of
                                        Lift (Mu v s) -> return (Lift (instSession v (Mu v s) s))
                                        _ -> return ty
          checkUnrolling m       = check' m

          -- TODO: I'm unconvinced that this is necessarily enough---it doesn't unroll fixed points
          -- below the top levels of types when comparing for equality.
          equals (Lift (Mu x s)) (Lift (Mu x' s')) = s == instSession x' (SVar x) s'
          equals (Lift (Mu x s)) (Lift s') = equals (Lift (instSession x (Mu x s) s)) (Lift s')
          equals (Lift s') (Lift (Mu x s)) = equals (Lift (instSession x (Mu x s) s)) (Lift s')
          equals t t'                      = t == t'

          check' :: Term -> Check Type
          check' Unit = return UnitType
          check' (EInt n) = return Int
          check' (Var x) = consume x
          check' (Link m n) =
              do t <- check m
                 t' <- check n
                 case (t, t') of
                   (Lift s, Lift s')
                       | duals s s' -> return (Lift OutTerm)
                       | otherwise -> fail ("    Sessions in link are not dual: " ++ show (pretty s) ++ " and " ++ show (pretty s'))
                   _ -> fail ("    Non-session arguments to link: " ++ show (pretty t) ++ " and " ++ show (pretty t'))
              where duals (Mu x s) (Nu y s') = duals s (instSession y (SVar x) s')
                    duals (Nu y s) (Mu x s') = duals s (instSession y (SVar x) s')
                    duals (Mu x s) s'        = duals (instSession x (Mu x s) s) s'
                    duals s (Mu x s')        = duals s (instSession x (Mu x s') s')
                    duals s s'               = s == dual s'
          check' (UnlLam x t m) =
              do u <- restrict (unlimited . typeFrom) (provide x t (check m))
                 return (UnlFun t u)
          check' (LinLam x t m) =
              do u <- provide x t (check m)
                 return (LinFun t u)
          check' (App m n) =
              do mty <- check m
                 nty <- check n
                 case mty of
                   v `LinFun` w
                       | equals v nty -> return w
                       | otherwise -> fail ("   Argument has type " ++ show (pretty nty) ++ " but expected " ++ show (pretty v))
                   v `UnlFun` w
                       | equals v nty -> return w
                       | otherwise -> fail ("   Argument has type " ++ show (pretty nty) ++ " but expected " ++ show (pretty v))
                   _ -> fail ("   Application of non-function of type " ++ show (pretty mty))
          check' (Pair m n) =
              do mty <- check m
                 nty <- check n
                 return (Tensor mty nty)
          check' (Let (BindName x) m n) =
              do t <- check m
                 if t == Lift InTerm && x `notElem` fv n
                 then do u <- check n
                         return u
                 else do u <- provide x t (check n)
                         return u
          check' (Let (BindPair x y) m n) =
              do mty <- checkUnrolling m
                 case mty of
                   Tensor xty yty ->
                       let isWeakened z zty = if zty == Lift InTerm && z `notElem` fv n then (z :) else id
                           weakened = isWeakened x xty (isWeakened y yty [])
                       in  do nty <- provide x xty (provide y yty (check n))
                              return nty
                   _ -> fail ("    Attempted to pattern-match non-pair of type " ++ show (pretty mty))
          check' (LetRec (x,b) f ps c m n) =
              do q <- fresh "Q"
                 mty <- provide f (foldr UnlFun (Lift (SVar q) `UnlFun` Lift OutTerm) ts) $
                             provide c (Lift (instSession x (SVar q) b)) $
                             foldr (\(x, t) m -> provide x t m) (check m) ps
                 nty <- provide f (foldr UnlFun (Lift (Nu x b) `UnlFun` Lift OutTerm) ts) (check n)
                 case mty of
                   Lift OutTerm -> return nty
                   _ -> fail ("    Unexpected type in letrec " ++ show (pretty mty))
              where (_, ts) = unzip ps
          check' (Corec c ci ts m n) =
              do cty <- consume c
                 case cty of
                   Lift (Nu x b) ->
                       do mty <- provide ci (Lift tsOut) (check m)
                          case mty of
                            Lift OutTerm ->
                                do nty <- provide ci (Lift tsIn) (restrict (const False) (provide c (Lift (instSession x tsOut b)) (check n)))
                                   case nty of
                                     Lift OutTerm -> return (Lift OutTerm)
                                     _ -> fail ("    Result of step term has unexpected type " ++ show (pretty nty))
                            _ -> fail ("    Result of establishing term has unexpected type " ++ show (pretty mty))
                   _ -> fail ("    Recursive channel in corec has unexpected type " ++ show (pretty cty))
              where tsOut = foldr Output OutTerm ts
                    tsIn  = foldr Input InTerm ts
          check' (Send m n) =
              do mty <- check m
                 nty <- checkUnrolling n
                 case nty of
                   Lift (Output v w)
                        | equals mty v -> return (Lift w)
                        | otherwise -> fail ("    Sent value has type " ++ show (pretty mty) ++ " but expected " ++ show (pretty v))
                   _ -> fail ("    Channel of send operation has unexpected type " ++ show (pretty nty))
          check' (Receive m) =
              do mty <- checkUnrolling m
                 case mty of
                   Lift (Input v w) -> return (v `Tensor` Lift w)
                   _ -> fail ("    Channel of receive operation has unexpected type " ++ show (pretty mty))
          check' (Select l m) =
              do mty <- checkUnrolling m
                 case mty of
                   Lift (Sum cs) -> do st <- lookupLabel l cs
                                       return (Lift st)
                   _             -> fail ("    Channel of select operation has unexepcted type " ++ show (pretty mty))
          check' (Case m bs@(_:_))
              | Just l <- duplicated bs = fail ("    Duplicated case label " ++ show (pretty l))
              | otherwise = do mty <- checkUnrolling m
                               case mty of
                                 Lift (Choice cs) -> do t:ts <- mapPar (checkBranch cs) bs
                                                        if all (t ==) ts
                                                        then return t
                                                        else fail ("   Divergent results of case branches:" ++ intercalate ", " (map (show . pretty) (nub (t:ts))))
                                 _                -> fail ("    Channel of case operation has unexpected type " ++ show (pretty mty))
              where duplicated [] = Nothing
                    duplicated ((l, _, _) : bs)
                        | or [l == l' | (l', _, _) <- bs] = Just l
                        | otherwise = duplicated bs
                    checkBranch :: [(String, Session)] -> (String, String, Term) -> Check Type
                    checkBranch cs (l, x, n) =
                        do s <- lookupLabel l cs
                           provide x (Lift s) (check n)
                    checkWeakening x t n p
                        | t == Lift InTerm && x `notElem` fv n = emptyIn x p
                        | otherwise = p

                    replace x y t = t'
                        where Right t' = CP.runM (CP.replace x y t)

          check' (EmptyCase m xs t) =
             do mty <- check m
                case mty of
                  Lift (Choice []) -> do mapM_ consume xs
                                         return t
                  _                -> fail ("    Channel of empty case operation has unexpected type " ++ show (pretty mty))

          check' (Fork x a m) =
              do mty <- provide x (Lift a) (check m)
                 case mty of
                   Lift OutTerm -> return (Lift (dual a))
                   _ -> fail ("    Argument to fork has unexpected type " ++ show (pretty mty))

          check' (Serve x a m) =
              do t <- provide x (Lift a) (check m)
                 case t of
                   Lift OutTerm ->
                       return (Lift (Service (dual a)))
                   _ -> fail ("    Argument to serve has unexpected type " ++ show (pretty t))

          check' (Request m) =
              do t <- checkUnrolling m
                 case t of
                   Lift (Service ty) ->
                     return (Lift ty)
                   _ -> fail("    Unexpected type of service channel " ++ show (pretty t))
          check' (SendType s m) =
              do mty <- checkUnrolling m
                 case mty of
                   Lift (OutputType v s') ->
                        return (Lift (instSession v s s'))
                   _ -> fail ("    Channel of send type operation has unexpected type " ++ show (pretty mty))
          check' (ReceiveType m) =
              do mty <- checkUnrolling m
                 case mty of
                   Lift (InputType v s') ->
                        return (Lift s')
                   _ -> fail ("    Channel of receive type operation has unexpected type " ++ show (pretty mty))

lookupLabel :: String -> [(String, Session)] -> Check Session
lookupLabel l [] = fail ("    Unable to find label " ++ l)
lookupLabel l ((l', s) : rest)
    |  l == l'   = return s
    | otherwise  = lookupLabel l rest

checkAgainst :: Term -> Type -> Check ()
checkAgainst te ty = do ty' <- check te
                        if ty == ty'
                        then return ()
                        else fail ("Expected type " ++ show (pretty ty) ++ " but actual type is " ++ show (pretty ty'))
