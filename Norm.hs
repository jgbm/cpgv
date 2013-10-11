module Norm where

import Check
import Control.Monad
import Data.List (intercalate, nub)
import Data.Maybe
import Syntax.AbsCP
import Syntax.PrintCP

import Debug.Trace

-- trace x y = y

--------------------------------------------------------------------------------
-- Free name and their manipulations
--------------------------------------------------------------------------------

-- The free names in an expression.

fn :: Proc -> [LIdent]
fn (Link x w)            = [x,w]
fn (Comp x _ p q)        = filter (x /=) (concatMap fn [p,q])
fn (Out x y p q)         = x : filter (y /=) (fn p) ++ fn q
fn (In x y p)            = x : filter (y /=) (fn p)
fn (Inl x p)             = x : fn p
fn (Inr x p)             = x : fn p
fn (Case x p q)          = x : concatMap fn [p,q]
fn (ServerAccept x y p)  = x : filter (y /=) (fn p)
fn (ClientRequest x y p) = x : filter (y /=) (fn p)
fn (SendType x a p)      = x : fn p
fn (ReceiveType x a p)   = x : fn p
fn (EmptyOut x)          = [x]
fn (EmptyIn x p)         = x : fn p
fn (EmptyCase x ys)      = x : ys

-- fln p returns the free "linear" names in p---that is, the free names that are
-- not used as the channels in ClientRequest forms.  This is used only to patch
-- up the list of discarded hypotheses when applying a commuting conversion to
-- an expression of the form nu x:A (x.case() | P).

fln :: Proc -> [LIdent]
fln (Link x w)            = [x,w]
fln (Comp x _ p q)        = filter (x /=) (concatMap fln [p,q])
fln (Out x y p q)         = x : filter (y /=) (fln p) ++ fln q
fln (In x y p)            = x : filter (y /=) (fln p)
fln (Inl x p)             = x : fln p
fln (Inr x p)             = x : fln p
fln (Case x p q)          = x : concatMap fln [p,q]
fln (ServerAccept x y p)  = x : filter (y /=) (fln p)
fln (ClientRequest x y p) = filter (y /=) (fln p)
fln (SendType x a p)      = x : fln p
fln (ReceiveType x a p)   = x : fln p
fln (EmptyOut x)          = [x]
fln (EmptyIn x p)         = x : fln p
fln (EmptyCase x ys)      = x : ys

-- Replace one variable by another---used, for example, when eliminating a cut
-- by the AxCut rule.

replace :: LIdent -> LIdent -> Proc -> Proc
replace x y = replace'
    where var z
              | x == z = y
              | otherwise = z

          replace' (Link z z') = Link (var z) (var z')
          replace' (Comp z a p q)
              | x == z    = Comp z a p q
              | otherwise = Comp z a (replace' p) (replace' q)
          replace' (Out z w p q)
              | x == w    = Out (var z) w p (replace' q)
              | otherwise = Out (var z) w (replace' p) (replace' q)
          replace' (In z w p)
              | x == w = In (var z) w p
              | otherwise = In z w (replace' p)
          replace' (Inl z p) = Inl (var z) (replace' p)
          replace' (Inr z p) = Inr (var z) (replace' p)
          replace' (Case z p q) = Case (var z) (replace' p) (replace' q)
          replace' (ServerAccept z w p)
              | x == w = ServerAccept (var z) w p
              | otherwise = ServerAccept (var z) w (replace' p)
          replace' (ClientRequest z w p)
              | x == w = ClientRequest (var z) w p
              | otherwise = ClientRequest (var z) w (replace' p)
          replace' (SendType z a p) = SendType (var z) a (replace' p)
          replace' (ReceiveType z a p) = ReceiveType (var z) a (replace' p)
          replace' (EmptyOut z) = EmptyOut (var z)
          replace' (EmptyIn z p) = EmptyIn (var z) (replace' p)
          replace' (EmptyCase z ws) = EmptyCase (var z) (map var ws)

--------------------------------------------------------------------------------
-- Types in terms
--------------------------------------------------------------------------------

-- Instantiate some type variable whenever it appears in a term---used in
-- ReceiveType.

instance HasTyVars Proc
    where inst x b = go
              where go (Link y z) = Link y z
                    go (Comp z a p q) = Comp z (inst x b a) (go p) (go q)
                    go (Out z y p q) = Out z y (go p) (go q)
                    go (In z y p) = In z y (go p)
                    go (Inl z p) = Inl z (go p)
                    go (Inr z p) = Inr z (go p)
                    go (Case z p q) = Case z (go p) (go q)
                    go (ServerAccept z y p) = ServerAccept z y (go p)
                    go (ClientRequest z y p) = ClientRequest z y (go p)
                    go (SendType z a p) = SendType z (inst x b a) (go p)
                    go (ReceiveType z x' p)
                        | x == x' = ReceiveType z x' p
                        | otherwise = ReceiveType z x' (go p)
                    go (EmptyOut z) = EmptyOut z
                    go (EmptyIn z p) = EmptyIn z (go p)
                    go (EmptyCase z ys) = EmptyCase z ys

--------------------------------------------------------------------------------
-- Normalization steps
--------------------------------------------------------------------------------

-- Principal cut reductions; "stepPrincipal p" returns "Just p'" if it was able
-- to eliminate a cut, and Nothing otherwise.

stepPrincipal :: Proc -> Maybe Proc
stepPrincipal p =
    case stepPrincipal1 p of
      Just (s, p') -> trace ("Reduced " ++ printTree p ++ "\nto " ++ printTree p' ++ "\nby " ++ s)
                            (Just p')
      Nothing      -> Nothing
    where trace x y = y

stepPrincipal1 :: Proc -> Maybe (String, Proc)
-- AxCut:
stepPrincipal1 (Comp x a (Link y z) p)
    | x == y = Just ("AxCut", replace x z p)
    | x == z = Just ("AxCut", replace x y p)
-- beta_times-par:
stepPrincipal1 (Comp x (a `Times` b) (Out z y p q) (In z' y' r))
    | x == z && x == z' && y == y' = Just ("beta_times-par", Comp y a p (Comp x b q r))
-- beta_plus-with (left):
stepPrincipal1 (Comp x (a `Plus` b) (Inl y p) (Case z q r))
    |  x == y && x == z = Just ("beta_plus-with (l)", Comp x a p q)
-- beta_plus-with (right):
stepPrincipal1 (Comp x (a `Plus` b) (Inr y p) (Case z q r))
    | x == y && x == z = Just ("beta_plus-with (r)", Comp x b p r)
-- beta_!C?:
stepPrincipal1 (Comp x (OfCourse a) (ServerAccept z w p) (ClientRequest z' w' q))
    | x == z && x == z' && w == w' && x `elem` fn q = Just ("beta_!C?", Comp x (OfCourse a) (ServerAccept z w p) (Comp w a p q))
-- beta_!?:
stepPrincipal1 (Comp x (OfCourse a) (ServerAccept z w p) (ClientRequest z' w' q))
    | x == z && x == z' && w == w' = Just ("beta_!?", Comp w a p q)
-- beta_!W:
stepPrincipal1 (Comp x (OfCourse a) (ServerAccept z w p) q)
    | x == z && z `notElem` fn q = Just ("beta_!W", q)
-- beta_exists-forall:
stepPrincipal1 (Comp x (Exists z b) (SendType y a p) (ReceiveType y' a' q))
    | x == y && x == y' = Just ("beta_exists-forall", Comp x (inst a' a b) p (inst a' a q))
-- beta_1-bottom:
stepPrincipal1 (Comp x One (EmptyOut z) (EmptyIn z' p))
    | x == z && x == z' = Just ("beta_1-bottom", p)
-- reduction under cut:
stepPrincipal1 (Comp x a p q) =
    case (stepPrincipal p, stepPrincipal q) of
      (Nothing, Nothing) -> Nothing
      (p', q')           -> Just ("Reduction under cut", Comp x a (fromMaybe p p') (fromMaybe q q'))
stepPrincipal1 p = Nothing

-- Commuting conversions.

stepCommuting :: Proc -> Maybe Proc
-- kappa_times-1
stepCommuting (Comp z a (Out x y p q) r)
    | z /= x && z `elem` fn p = Just (Out x y (Comp z a p r) q)
-- kappa_times-2
stepCommuting (Comp z a (Out x y p q) r)
    | z /= x && z `elem` fn q = Just (Out x y p (Comp z a q r))
-- kappa_par
stepCommuting (Comp z a (In x y p) q)
    | z /= x = Just (In x y (Comp z a p q))
-- kappa_plus-1
stepCommuting (Comp z a (Inl x p) q)
    | z /= x = Just (Inl x (Comp z a p q))
-- kapppa_plus-2
stepCommuting (Comp z a (Inr x p) q)
    | z /= x = Just (Inr x (Comp z a p q))
-- kappa_with
stepCommuting (Comp z a (Case x p q) r)
    | z /= x = Just (Case x (Comp z a p r) (Comp z a q r))
-- kappa_bang
stepCommuting (Comp z a (ServerAccept x y p) q)
    | z /= x = Just (ServerAccept x y (Comp z a p q))
-- kappa_question
stepCommuting (Comp z a (ClientRequest x y p) q)
    | z /= x = Just (ClientRequest x y (Comp z a p q))
-- kappa_exists
stepCommuting (Comp z a (SendType x b p) q)
    | z /= x = Just (SendType x b (Comp z a p q))
-- kappa_forall
stepCommuting (Comp z a (ReceiveType x b p) q)
    | z /= x = Just (ReceiveType x b (Comp z a p q))
-- kappa_bottom
stepCommuting (Comp z a (EmptyIn x p) q)
    | z /= x = Just (EmptyIn x (Comp z a p q))
-- kappa_top
stepCommuting (Comp z a (EmptyCase x ys) q)
    | z /= x = Just (EmptyCase x (filter (x /=) (ys ++ fln q)))
stepCommuting p = Nothing

-- Expressions equivalent, either by swapping the order of cut arguments or by
-- commuting cut arguments, to the original expression.

equiv p@Comp{} = nub (ps ++ concatMap (expandOne (ps ++ ps')) ps')
    where ps = expandOne [] p
          ps' = filter (`notElem` ps) [Comp x a p' q' | Comp x a p q <- ps, p' <- equiv p, q' <- equiv q]

          expandOne ps p = p : concatMap (expandOne (p : ps' ++ ps)) ps'
              where ps' = filter (`notElem` ps) (swapped p : reassocLeft p ++ reassocRight p)

                    swapped (Comp x a p q) = Comp x (dual a) q p
                    reassocLeft (Comp x a p q) =
                        case p of
                          Comp y b p' q'
                              | x `notElem` fn p' -> [Comp y b p' (Comp x a q' q)]
                          _                       -> []
                    reassocRight (Comp x a p q) =
                        case q of
                          Comp y b p' q'
                              | x `notElem` fn q' -> [Comp y b (Comp x a p p') q']
                          _                       -> []
equiv p = [p]


-- Normalization is implemented as a simple loop.  As long as one of the
-- principal cut reductions applies to the input expression, or to any
-- expression equivalent to the input expression, normalization loops on the
-- result.  Otherwise, it attempts to apply commuting conversions and finishes.

normalize :: Proc -> Behavior -> Proc
normalize p b =
    case msum (map stepPrincipal ps) of
      Nothing -> fromMaybe p (msum (map stepCommuting ps))
      Just p' -> case runCheck (check p') b of
                   Left err -> error (unlines ["Normalization went wrong! Last good step was:",
                                               "   " ++ printTree p,
                                               "and first bad step was:",
                                               "   " ++ printTree p'])
                   Right _ -> normalize p' b
    where ps = equiv p

-- As a thin layer of verification, this applies the checking operation both
-- before and after normalization, assuring that the normalized expression has
-- the same behavior as the un-normalized one.

ncheck :: Proc -> Behavior -> Either String Proc
ncheck p b =
    case runCheck (check p) b of
      Left err -> Left err
      Right _  -> let p' = normalize p b
                  in  case runCheck (check p') b of
                        Left err -> Left ("Error introduced by normalization:\n" ++ err ++
                                          "\nPre-normalization term was: " ++ printTree p ++
                                          "\nand post-normalization term was: " ++ printTree p')
                        Right _  -> Right p'
