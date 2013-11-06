{-# LANGUAGE PatternGuards #-}
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
fn (Inj x l p)           = x : fn p
fn (Case x bs)           = x : concat [fn p | Branch l p <- bs]
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
fln (Inj x l p)           = x : fln p
fln (Case x bs)           = x : concat [fn p | Branch l p <- bs]
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
              | otherwise = In (var z) w (replace' p)
          replace' (Inj z l p) = Inj (var z) l (replace' p)
          replace' (Case z bs) = Case (var z) [Branch l (replace' p) | Branch l p <- bs]
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
                    go (Inj x l p) = Inj x l (go p)
                    go (Case z bs) = Case z [Branch l (go p) | Branch l p <- bs]
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

renameBoundVariable :: LIdent -> Proc -> LIdent -> Proc -> (LIdent, Proc, Proc)
renameBoundVariable x p x' p'
    | x == x' = (x, p, p')
    | x `notElem` fn p' = (x, p, replace x' x p')
    | x' `notElem` fn p = (x', replace x x' p, p')
    | otherwise = (n, replace x n p, replace x' n p')
    where (n:_)    = filter (\i -> i `notElem` fn p && i `notElem` fn p') newNames
          newNames = [LIdent (s ++ show i) | i <- [0..], LIdent s <- [x, x']]

-- Principal cut reductions; "stepPrincipal p" returns "Just p'" if it was able
-- to eliminate a cut, and Nothing otherwise.

stepPrincipal :: Proc -> Maybe Proc
-- AxCut:
stepPrincipal (Comp x a (Link y z) p)
    | x == y = Just (replace x z p)
    | x == z = Just (replace x y p)
-- beta_times-par:
stepPrincipal (Comp x (a `Times` b) (Out z y p q) (In z' y' r))
    | x == z && x == z' = Just (Comp y'' a p' (Comp x b q r'))
    where (y'', p', r') = renameBoundVariable y p y' r
--beta_plus-with (labelled):
stepPrincipal (Comp x (Plus lts) (Inj y l p) (Case z bs))
    | x == y, x == z, Just a <- lookupType lts, Just q <- lookupBranch bs = Just (Comp x a p q)
    where lookupType [] = Nothing
          lookupType (Label l' a : rest)
              | l == l' = Just a
              | otherwise = lookupType rest
          lookupBranch [] = Nothing
          lookupBranch (Branch l' q : rest)
              | l == l' = Just q
              | otherwise = lookupBranch rest
-- beta_!C?:
stepPrincipal (Comp x (OfCourse a) (ServerAccept z w p) (ClientRequest z' w' q))
    | x == z && x == z' && x `elem` fn q = Just (Comp x (OfCourse a) (ServerAccept z w p) (Comp w'' a p' q'))
    where (w'', p', q') = renameBoundVariable w p w' q
-- beta_!?:
stepPrincipal (Comp x (OfCourse a) (ServerAccept z w p) (ClientRequest z' w' q))
    | x == z && x == z' = Just (Comp w'' a p' q')
    where (w'', p', q') = renameBoundVariable w p w' q
-- beta_!W:
stepPrincipal (Comp x (OfCourse a) (ServerAccept z w p) q)
    | x == z && z `notElem` fn q = Just q
-- beta_exists-forall:
stepPrincipal (Comp x (Exists z b) (SendType y a p) (ReceiveType y' a' q))
    | x == y && x == y' = Just (Comp x (inst a' a b) p (inst a' a q))
-- beta_1-bottom:
stepPrincipal (Comp x One (EmptyOut z) (EmptyIn z' p))
    | x == z && x == z' = Just p
-- reduction under cut:
stepPrincipal (Comp x a p q) =
    case (stepPrincipal p, stepPrincipal q) of
      (Nothing, Nothing) -> Nothing
      (Just p', _)  -> Just (Comp x a p' q)
      (Nothing, Just q') -> Just (Comp x a p q')
stepPrincipal p = Nothing

-- Commuting conversions.

stepCommuting :: Proc -> Maybe Proc
-- kappa_times-1
stepCommuting (Comp z a (Out x y p q) r)
    | z /= x && z `elem` fn p && z `notElem` fn q = Just (Out x y (Comp z a p r) q)
-- kappa_times-2
stepCommuting (Comp z a (Out x y p q) r)
    | z /= x && z `elem` fn q && z `notElem` fn p = Just (Out x y p (Comp z a q r))
-- kappa_par
stepCommuting (Comp z a (In x y p) q)
    | z /= x = Just (In x y (Comp z a p q))
-- kappa_plus-labelled
stepCommuting (Comp z a (Inj x l p) q)
    | z /= x = Just (Inj x l (Comp z a p q))
-- kappa_with-labelled
stepCommuting (Comp z a (Case x bs) r)
    | z /= x = Just (Case x [Branch l (Comp z a p r) | Branch l p <- bs])
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

equivUnder r@Comp{}              = [Comp x a p' q' | Comp x a p q <- equiv r, p' <- equivUnder p, q' <- equivUnder q]
equivUnder (Out x y p q)         = [Out x y p' q' | p' <- equivUnder p, q' <- equivUnder q]
equivUnder (In x y p)            = In x y `fmap` equivUnder p
equivUnder (Inj x l p)           = Inj x l `fmap` equivUnder p
equivUnder (Case x bs)           = [Case x bs' | bs' <- equivBranches bs]
    where equivBranches [] = [[]]
          equivBranches (Branch l p : rest) = [Branch l p' : rest' | p' <- equivUnder p, rest' <- equivBranches rest]
equivUnder (ServerAccept x y p)  = ServerAccept x y `fmap` equivUnder p
equivUnder (ClientRequest x y p) = ClientRequest x y `fmap` equivUnder p
equivUnder (SendType x a p)      = SendType x a `fmap` equivUnder p
equivUnder (ReceiveType x a p)   = ReceiveType x a `fmap` equivUnder p
equivUnder (EmptyIn x p)         = EmptyIn x `fmap` equivUnder p
equivUnder p                     = [p]

(f `orElse` g) x = case f x of
                     Nothing -> g x
                     Just v  -> Just v

stepUnder :: (Proc -> Maybe Proc) -> Proc -> Maybe Proc
stepUnder stepper = stepper `orElse` into
    where firstOf f p q =
              case (stepUnder stepper p, stepUnder stepper q) of
                (Just p', _) -> Just (f p' q)
                (_, Just q') -> Just (f p q')
                _            -> Nothing

          into (Link w x) = Nothing
          into (Comp x a p q) = firstOf (Comp x a) p q
          into (Out x y p q) = firstOf (Out x y) p q
          into (In x y p) = In x y `fmap` stepUnder stepper p
          into (Inj x l p) = Inj x l `fmap` stepUnder stepper p
          into (Case x bs) = Case x `fmap` intoBranches bs
              where intoBranches [] = Nothing
                    intoBranches (Branch l p : rest) =
                        case stepUnder stepper p of
                          Just p' -> Just (Branch l p' : rest)
                          Nothing -> (Branch l p :) `fmap` intoBranches rest
          into (ServerAccept x y p) = ServerAccept x y `fmap` stepUnder stepper p
          into (ClientRequest x y p) = ClientRequest x y `fmap` stepUnder stepper p
          into (SendType x a p) = SendType x a `fmap` stepUnder stepper p
          into (ReceiveType x a p) = ReceiveType x a `fmap` stepUnder stepper p
          into (EmptyOut x) = Nothing
          into (EmptyIn x p) = EmptyIn x `fmap` stepUnder stepper p
          into (EmptyCase x ys) = Nothing


-- Normalization is implemented as a simple loop.  As long as one of the
-- principal cut reductions applies to the input expression, or to any
-- expression equivalent to the input expression, normalization loops on the
-- result.  Otherwise, it attempts to apply commuting conversions and finishes.
-- a thin layer of verification, this applies the checking operation both before
-- and after normalization, assuring that the normalized expression has the same
-- behavior as the un-normalized one.

normalize :: Proc -> Behavior -> (Proc, Proc)
normalize p b = let p' = execute p in (p', simplify p')
    where execute p = case msum (map stepPrincipal ps) of
                        Nothing -> fromMaybe p (msum (map stepCommuting ps))
                        Just p' -> case runCheck (check p') b of
                                     Left err -> error (unlines ["Execution went wrong! Last good step was:",
                                                                 "   " ++ printTree p,
                                                                 "and first bad step was:",
                                                                 "   " ++ printTree p'])
                                     Right _ -> execute p'
              where ps = equiv p

          simplify p = case msum (map (stepUnder stepPrincipal `orElse` stepUnder stepCommuting) (equivUnder p)) of
                         Nothing -> p
                         Just p' -> case runCheck (check p') b of
                                      Left err -> error (unlines ["Simplification went wrong! (" ++ err ++ ") Last good step was:",
                                                                  "   " ++ printTree p,
                                                                  "and first bad step was:",
                                                                  "   " ++ printTree p'])
                                      Right _ -> simplify p'