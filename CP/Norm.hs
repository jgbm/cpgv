{-# LANGUAGE PatternGuards, TupleSections #-}
module CP.Norm where

import Control.Monad.Error
import CP.Check
import Data.List (intercalate, nub)
import Data.Maybe
import CP.Syntax
import CP.Printer

--------------------------------------------------------------------------------
-- Operators (types with holes)

type Op = (String, Prop)

appl :: Op -> Prop -> Prop
appl (x, b) a = inst x a b

dualOp :: Op -> Op
dualOp (x, b) = (x, dual (appl (x, b) (Neg x)))

--------------------------------------------------------------------------------
-- Free name and their manipulations
--------------------------------------------------------------------------------

-- The free names in an expression.

fn :: Proc -> [String]
fn (Link x w)          = [x,w]
fn (Cut x _ p q)       = filter (x /=) (concatMap fn [p,q])
fn (Out x y p q)       = x : filter (y /=) (fn p) ++ fn q
fn (In x y p)          = x : filter (y /=) (fn p)
fn (Select x l p)      = x : fn p
fn (Case x bs)         = x : concatMap (fn . snd) bs
fn (Unroll x p)        = x : fn p
fn (Roll x y a p q)    = x : filter (y /=) (fn p ++ fn q)
fn (Replicate x y p)   = x : filter (y /=) (fn p)
fn (Derelict x y p)    = x : filter (y /=) (fn p)
fn (SendProp x a p)    = x : fn p
fn (ReceiveProp x a p) = x : fn p
fn (EmptyOut x)        = [x]
fn (EmptyIn x p)       = x : fn p
fn (EmptyCase x ys)    = x : ys
fn (Unk ys)            = ys

-- fln p returns the free "linear" names in p---that is, the free names that are
-- not used as the channels in ClientRequest forms.  This is used only to patch
-- up the list of discarded hypotheses when applying a commuting conversion to
-- an expression of the form nu x:A (x.case() | P).

fln :: Proc -> [String]
fln (Link x w)          = [x,w]
fln (Cut x _ p q)       = filter (x /=) (concatMap fln [p,q])
fln (Out x y p q)       = x : filter (y /=) (fln p) ++ fln q
fln (In x y p)          = x : filter (y /=) (fln p)
fln (Select x l p)      = x : fln p
fln (Case x bs)         = x : concatMap (fln . snd) bs
fln (Unroll x p)        = x : fn p
fln (Roll x y a p q)    = x : filter (y /=) (fn p ++ fn q)
fln (Replicate x y p)   = x : filter (y /=) (fln p)
fln (Derelict x y p)    = filter (y /=) (fln p)
fln (SendProp x a p)    = x : fln p
fln (ReceiveProp x a p) = x : fln p
fln (EmptyOut x)        = [x]
fln (EmptyIn x p)       = x : fln p
fln (EmptyCase x ys)    = x : ys
fln (Unk ys)            = ys

-- Replace one variable by another---used, for example, when eliminating a cut
-- by the AxCut rule.

--------------------------------------------------------------------------------
-- Props in terms
--------------------------------------------------------------------------------

-- Instantiate some type variable whenever it appears in a term---used in
-- ReceiveProp.

instance HasTyVars Proc
    where inst x b = go
              where go (Link y z) = Link y z
                    go (Cut z a p q) = Cut z (inst x b a) (go p) (go q)
                    go (Out z y p q) = Out z y (go p) (go q)
                    go (In z y p) = In z y (go p)
                    go (Select x l p) = Select x l (go p)
                    go (Case z bs) = Case z [(l,) (go p) | (l, p) <- bs]
                    go (Unroll z p) = Unroll z (go p)
                    go (Roll z w a p q) = Roll z w (inst x b a) (go p) (go q)
                    go (Replicate z y p) = Replicate z y (go p)
                    go (Derelict z y p) = Derelict z y (go p)
                    go (SendProp z a p) = SendProp z (inst x b a) (go p)
                    go (ReceiveProp z x' p)
                        | x == x' = ReceiveProp z x' p
                        | otherwise = ReceiveProp z x' (go p)
                    go (EmptyOut z) = EmptyOut z
                    go (EmptyIn z p) = EmptyIn z (go p)
                    go (EmptyCase z ys) = EmptyCase z ys
                    go (Unk ys) = Unk ys

--------------------------------------------------------------------------------
-- Freshalization steps
--------------------------------------------------------------------------------

renameBoundVariable :: String -> Proc -> String -> Proc -> M (String, Proc, Proc)
renameBoundVariable x p x' p'
    | x == x' = return (x, p, p')
    | x `notElem` fn p' = liftM (x, p,) (replace x' x p')
    | x' `notElem` fn p = liftM (x',, p') (replace x x' p)
    | otherwise = do n <- fresh x
                     liftM2 (n,,) (replace x n p) (replace x' n p')

-- Principal cut reductions; "stepPrincipal p" returns "Just p'" if it was able
-- to eliminate a cut, and Nothing otherwise.

stepPrincipal :: Proc -> M Proc
-- AxCut:
stepPrincipal (Cut x a (Link y z) p)
    | x == y = replace x z p
    | x == z = replace x y p
-- beta_times-par:
stepPrincipal (Cut x (a `Times` b) (Out z y p q) (In z' y' r))
    | x == z && x == z' = do (y'', p', r') <- renameBoundVariable y p y' r
                             return (Cut y'' a p' (Cut x b q r'))
--beta_plus-with (labelled):
stepPrincipal (Cut x (Plus lts) (Select y l p) (Case z bs))
    | x == y, x == z, Just a <- lookup l lts, Just q <- lookup l bs = return (Cut x a p q)
-- beta_exists-forall:
stepPrincipal (Cut x (Exists z b) (SendProp y a p) (ReceiveProp y' a' q))
    | x == y && x == y' = return (Cut x (inst a' a b) p (inst a' a q))
-- beta_1-bottom:
stepPrincipal (Cut x One (EmptyOut z) (EmptyIn z' p))
    | x == z && x == z' = return p
-- beta_!C?:
stepPrincipal (Cut x (OfCourse a) (Replicate z w p) (Derelict z' w' q))
    | x == z && x == z' && x `elem` fn q = do (w'', p', q') <- renameBoundVariable w p w' q
                                              return  (Cut x (OfCourse a) (Replicate z w p) (Cut w'' a p' q'))
-- beta_!?:
stepPrincipal (Cut x (OfCourse a) (Replicate z w p) (Derelict z' w' q))
    | x == z && x == z' = do (w'', p', q') <- renameBoundVariable w p w' q
                             return (Cut w'' a p' q')
-- beta_!W:
stepPrincipal (Cut x (OfCourse a) (Replicate z w p) q)
    | x == z && z `notElem` fn q = return q
-- beta_mu-nu
stepPrincipal (Cut x (Mu t a) (Unroll x' p) (Roll x'' y s q r))
    |  x == x' && x == x'' = do z <- fresh "z"
                                r' <- replace x z r
                                recurse <- funct b x z (Roll z y s (Link x y) r')
                                p' <- replace x z p
                                if y `elem` fn p
                                then do y' <- fresh y
                                        q' <- replace y y' q
                                        r' <- replace y y' r
                                        return (Cut y' s q'
                                                (Cut x (bbar `appl` s) r'
                                                 (Cut z (bbar `appl` nu bbar) recurse p')))
                                else return (Cut y s q
                                             (Cut x (bbar `appl` s) r
                                              (Cut z (bbar `appl` nu bbar) recurse p')))
    where b = (t, a)
          bbar = dualOp b
          nu (t, a) = Nu t a
          -- assuming that there are propositions A and B such that q |- x:A,w:B,
          -- funct c x w q |- x:c A,w:cbar B
          funct (t,c) x w q
              | t `notElem` ftv c = return (Link x w)
          funct (t, Var t' []) x w q
              | t == t' = return q
          funct (t, c1 `Times` c2) x w q =
              do y <- fresh "y"
                 z <- fresh "z"
                 q' <- replace x y =<< replace z w q
                 left <- funct (t, c1) y z q'
                 right <- funct (t, c2) x w q
                 return (In w z (Out x y left right))
          funct (t, c1 `Par` c2) x w q =
              do y <- fresh "y"
                 z <- fresh "z"
                 q' <- replace x y =<< replace w z q
                 left <- funct (t, c1) y z q'
                 right <- funct (t, c2) x w q
                 return (In x y (Out w z left right))
          funct (t, Plus lts) x w q = Case w `fmap` mapM branch lts
              where branch (l, c) = ((l,) . Select x l) `fmap` funct (t, c) x w q
          funct (t, With lts) x w q = Case x `fmap` mapM branch lts
              where branch (l, c) = ((l,) . Select w l) `fmap` funct (t, c) x w q
          funct (t, a) _ _ _ = error ("Unimplemented: functoriality for " ++ t ++ "." ++ show (pretty a))

-- reduction under cut:
stepPrincipal (Cut x a p q) =
    (do p' <- stepPrincipal p
        return (Cut x a p' q)) `mplus`
    (do q' <- stepPrincipal q
        return (Cut x a p q'))
stepPrincipal p = throwError "No applicable principal cut reduction"

-- Commuting conversions.

stepCommuting :: Proc -> M Proc
-- kappa_times-1
stepCommuting (Cut z a (Out x y p q) r)
    | z /= x && z `elem` fn p && z `notElem` fn q = return (Out x y (Cut z a p r) q)
-- kappa_times-2
stepCommuting (Cut z a (Out x y p q) r)
    | z /= x && z `elem` fn q && z `notElem` fn p = return (Out x y p (Cut z a q r))
-- kappa_par
stepCommuting (Cut z a (In x y p) q)
    | z /= x = return (In x y (Cut z a p q))
-- kappa_plus-labelled
stepCommuting (Cut z a (Select x l p) q)
    | z /= x = return (Select x l (Cut z a p q))
-- kappa_with-labelled
stepCommuting (Cut z a (Case x bs) r)
    | z /= x = return (Case x [(l, Cut z a p r) | (l, p) <- bs])
-- kappa_bang
stepCommuting (Cut z a (Replicate x y p) q)
    | z /= x = return (Replicate x y (Cut z a p q))
-- kappa_question
stepCommuting (Cut z a (Derelict x y p) q)
    | z /= x = return (Derelict x y (Cut z a p q))
-- kappa_exists
stepCommuting (Cut z a (SendProp x b p) q)
    | z /= x = return (SendProp x b (Cut z a p q))
-- kappa_forall
stepCommuting (Cut z a (ReceiveProp x b p) q)
    | z /= x = return (ReceiveProp x b (Cut z a p q))
-- kappa_bottom
stepCommuting (Cut z a (EmptyIn x p) q)
    | z /= x = return (EmptyIn x (Cut z a p q))
-- kappa_top
stepCommuting (Cut z a (EmptyCase x ys) q)
    | z /= x = return (EmptyCase x (filter (x /=) (ys ++ fln q)))
-- kappa_mu
stepCommuting (Cut z a (Unroll x p) q)
    | z /= x = return (Unroll x (Cut z a p q))
stepCommuting p = throwError "No applicable commuting conversion"

-- Expressions equivalent, either by swapping the order of cut arguments or by
-- commuting cut arguments, to the original expression.

equiv p@Cut{} = nub (ps ++ concatMap (expandOne (ps ++ ps')) ps')
    where ps = expandOne [] p
          ps' = filter (`notElem` ps) [Cut x a p' q' | Cut x a p q <- ps, p' <- equiv p, q' <- equiv q]

          expandOne ps p = p : concatMap (expandOne (p : ps' ++ ps)) ps'
              where ps' = filter (`notElem` ps) (swapped p : reassocLeft p ++ reassocRight p)
                    swapped (Cut x a p q) = Cut x (dual a) q p
                    reassocLeft (Cut x a (Cut y b p' q') q)
                        | x `notElem` fn p', y `notElem` fn q = [Cut y b p' (Cut x a q' q)]
                    reassocLeft _ = []
                    reassocRight (Cut x a p (Cut y b p' q'))
                        | x `notElem` fn q', y `notElem` fn p = [Cut y b (Cut x a p p') q']
                    reassocRight _ = []
equiv p = [p]

equivUnder r@Cut{}               = [Cut x a p' q' | Cut x a p q <- equiv r, p' <- equivUnder p, q' <- equivUnder q]
equivUnder (Out x y p q)         = [Out x y p' q' | p' <- equivUnder p, q' <- equivUnder q]
equivUnder (In x y p)            = In x y `fmap` equivUnder p
equivUnder (Select x l p)        = Select x l `fmap` equivUnder p
equivUnder (Case x bs)           = [Case x bs' | bs' <- equivBranches bs]
    where equivBranches [] = [[]]
          equivBranches ((l, p) : rest) = [(l, p') : rest' | p' <- equivUnder p, rest' <- equivBranches rest]
equivUnder (Unroll x p)          = Unroll x `fmap` equivUnder p
equivUnder (Roll x y a p q)      = [Roll x y a p' q' | p' <- equivUnder p, q' <- equivUnder q]
equivUnder (Replicate x y p)     = Replicate x y `fmap` equivUnder p
equivUnder (Derelict x y p)      = Derelict x y `fmap` equivUnder p
equivUnder (SendProp x a p)      = SendProp x a `fmap` equivUnder p
equivUnder (ReceiveProp x a p)   = ReceiveProp x a `fmap` equivUnder p
equivUnder (EmptyIn x p)         = EmptyIn x `fmap` equivUnder p
equivUnder p                     = [p]

stepUnder :: (Proc -> M Proc) -> Proc -> M Proc
stepUnder stepper p = stepper p `mplus` into p
    where firstOf f p q =
              (do p' <- stepUnder stepper p
                  return (f p' q)) `mplus`
              (do q' <- stepUnder stepper q
                  return (f p q'))

          into (Link w x) = throwError "No subexpressions"
          into (Cut x a p q) = firstOf (Cut x a) p q
          into (Out x y p q) = firstOf (Out x y) p q
          into (In x y p) = In x y `fmap` stepUnder stepper p
          into (Select x l p) = Select x l `fmap` stepUnder stepper p
          into (Case x bs) = Case x `fmap` intoBranches bs
              where intoBranches [] = throwError "Exhausted branches"
                    intoBranches ((l, p) : rest) =
                        (do p' <- stepUnder stepper p
                            return ((l, p') : rest)) `mplus`
                        (((l, p) :) `fmap` intoBranches rest)
          into (Unroll x p) = Unroll x `fmap` stepUnder stepper p
          into (Roll x y a p q) = firstOf (Roll x y a) p q
          into (Replicate x y p) = Replicate x y `fmap` stepUnder stepper p
          into (Derelict x y p) = Derelict x y `fmap` stepUnder stepper p
          into (SendProp x a p) = SendProp x a `fmap` stepUnder stepper p
          into (ReceiveProp x a p) = ReceiveProp x a `fmap` stepUnder stepper p
          into (EmptyOut x) = throwError "No subexpressions"
          into (EmptyIn x p) = EmptyIn x `fmap` stepUnder stepper p
          into (EmptyCase x ys) = throwError "No subexpressions"
          into Unk{} = throwError "No subexpressions"


-- Malization is implemented as a simple loop.  As long as one of the
-- principal cut reductions applies to the input expression, or to any
-- expression equivalent to the input expression, normalization loops on the
-- result.  Otherwise, it attempts to apply commuting conversions and finishes.
-- a thin layer of verification, this applies the checking operation both before
-- and after normalization, assuring that the normalized expression has the same
-- behavior as the un-normalized one.

normalize :: Proc -> Behavior -> M (Proc, Proc)
normalize p b = do p' <- execute p
                   (p',) `fmap` simplify p'
    where execute p = do stepped <- (Just `fmap` msum (map stepPrincipal ps)) `catchError` const (return Nothing)
                         case stepped of
                           Nothing -> msum (map stepCommuting ps) `catchError` const (return p)
                           Just p' -> case runCheck (check p') b of
                                        (_, Left err) -> throwError (errorMessage p p' err)
                                        (_, Right _) -> execute p'

              where ps = equiv p
                    showCP c = displayS (renderPretty 0.8 120 (pretty c)) ""
                    errorMessage p p' e = unlines ["Execution went wrong:",
                                                   e,
                                                   "Last good step was:",
                                                   showCP p,
                                                   "and first bad step was:",
                                                   showCP p']

          simplify p = do stepped <- (Just `fmap` msum [stepUnder stepPrincipal p' `mplus` stepUnder stepCommuting p' | p' <- equivUnder p])
                                     `catchError` const (return Nothing)
                          case stepped of
                            Nothing -> return p
                            Just p' ->
                                case runCheck (check p') b of
                                  (_, Left err) -> throwError (unlines ["Simplification went wrong! (" ++ err ++ ") Last good step was:",
                                                                        "   " ++ showCP p,
                                                                        "and first bad step was:",
                                                                        "   " ++ showCP p'])
                                  (_, Right _) -> simplify p'
              where showCP c = displayS (renderPretty 0.8 120 (pretty c)) ""
