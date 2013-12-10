module CP.Check where

import Control.Monad
import Data.List
import CP.Syntax
import CP.Printer

import Debug.Trace

--------------------------------------------------------------------------------
-- Utility operations on types
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Negating types

dual :: Prop -> Prop
dual (Dual p)      = p
-- Variables
dual (Var s [])    = Neg s
dual (Neg s)       = Var s []
-- Multiplicative combinators
dual (a `Times` b) = dual a `Par` dual b
dual (a `Par` b)   = dual a `Times` dual b
dual One           = Bottom
dual Bottom        = One
-- Additive combinators
dual (Plus lts)    = With [(l, dual t) | (l, t) <- lts]
dual (With lts)    = Plus [(l, dual t) | (l, t) <- lts]
-- Fixed-point combinators
dual (Mu x a)      = Nu x (dual (inst x (Neg x) a))
dual (Nu x a)      = Mu x (dual (inst x (Neg x) a))
-- Exponentials
dual (OfCourse a) = WhyNot (dual a)
dual (WhyNot a) = OfCourse (dual a)
-- Quantifiers
dual (ForAll x a)  = Exists x (dual a)
dual (Exists x a)  = ForAll x (dual a)

--------------------------------------------------------------------------------
-- Free type variables
ftv :: Prop -> [String]
-- Variables
ftv (Var s []) = [s]
ftv (Neg s)    = [s]
-- Multiplicative combinators
ftv (a `Times` b) = concatMap ftv [a,b]
ftv (a `Par` b) = concatMap ftv [a,b]
ftv One = []
ftv Bottom = []
-- Additive combinators
ftv (Plus ls) = concatMap (ftv . snd) ls
ftv (With ls) = concatMap (ftv . snd) ls
-- Fixed-point combinators
ftv (Mu x a) = filter (x /=) (ftv a)
ftv (Nu x a) = filter (x /=) (ftv a)
-- Exponentials
ftv (OfCourse a) = ftv a
ftv (WhyNot a) = ftv a
-- Quantifiers
ftv (ForAll x a) = filter (x /=) (ftv a)
ftv (Exists x a) = filter (x /=) (ftv a)

--------------------------------------------------------------------------------
-- Instantiating type variables
class HasTyVars t
    where inst :: String -> Prop -> t -> t

instBinder x c b x' a
    | x == x' = b x a
    | otherwise = b x' (inst x c a)

instance HasTyVars Prop
    where -- Variables
          inst x c (Var x' []) | x == x' = c
                               | otherwise = Var x' []
          inst x c (Neg x') | x == x' = dual c
                            | otherwise = Neg x'
          -- Multiplicative combinators
          inst x c (a `Times` b) = inst x c a `Times` inst x c b
          inst x c (a `Par` b) = inst x c a `Par` inst x c b
          inst _ _ One = One
          inst _ _ Bottom = Bottom
          -- Additive combinators
          inst x c (Plus lts) = Plus [(l, inst x c t) | (l, t) <- lts]
          inst x c (With lts) = With [(l, inst x c t) | (l, t) <- lts]
          -- Fixed-point combinators
          inst x c (Mu x' a) = instBinder x c Mu x' a
          inst x c (Nu x' a) = instBinder x c Nu x' a
          -- Exponentials
          inst x c (OfCourse a) = OfCourse (inst x c a)
          inst x c (WhyNot a) = WhyNot (inst x c a)
          -- Quantifiers
          inst x c (ForAll x' a) = instBinder x c ForAll x' a
          inst x c (Exists x' a) = instBinder x c Exists x' a

isWhyNot (WhyNot _) = True
isWhyNot _          = False

--------------------------------------------------------------------------------
-- Checking monad.  Each checking operation takes a list of assumptions as
-- arguments, and produces either an error message, or a (reduced) list of
-- arguments as a result.
--------------------------------------------------------------------------------

type Behavior = [(String, Prop)]
newtype Check t = Check { runCheck :: Behavior                -- initial context
                                   -> ([Behavior],            -- traced contexts
                                       Either String          -- typing failure
                                              (t, Behavior))  -- remaining context
                        }

instance Functor Check
    where fmap f (Check g) = Check (\b -> case g b of
                                            (t, Left err) -> (t, Left err)
                                            (t, Right (v, b')) -> (t, Right (f v, b')))

instance Monad Check
    where return v = Check (\b -> ([], Right (v, b)))
          Check f >>= g = Check (\b -> case f b of
                                         (t, Left err) -> (t, Left err)
                                         (t, Right (v, b')) ->
                                             case runCheck (g v) b' of
                                               (t', Left err) -> (t ++ t', Left err)
                                               (t', Right (v', b'')) -> (t ++ t', Right (v', b'')))
          fail s = Check (\_ -> ([], Left s))

-- Looks up the provided identifier in the assumptions, removing its typing from
-- the assumption list.

consume :: String -> Check Prop
consume x = Check (\b -> ([], case partition ((x ==) . fst) b of
                                ([], _) -> Left ("No type for " ++ x)
                                ([(_, t)], b')
                                    | isWhyNot t -> Right (t, b)
                                    | otherwise  -> Right (t, b')
                                _ -> error ("Internal failure: multiple bindings of " ++ x ++ " in behavior.")))

-- Adds a binding to the assumption list for the purposes of the subcomputation.
-- Two wrinkles:
--  - We insist that the binding is used during the subcomputation.
--  - Should the new binding shadow an existing binding, that binding is removed
--    from the assumptions for the purposes of the subcomputation, and
--    reintroduced in the result of provide.

provide :: String -> Prop -> Check t -> Check t
provide x t c = Check (\b -> let (included, excluded) = partition ((x /=) . fst) b
                             in  case runCheck c ((x, t) : included) of
                                   (t, Left err) -> (t, Left err)
                                   (t, Right (v, b')) -> (t, let (xs, b'') = partition ((x ==) . fst) b'
                                                             in  if any (not . isWhyNot . snd) xs
                                                                 then Left ("Failed to consume bindings " ++ intercalate "," [x ++ ": " ++ show (pretty t) | (x, t) <- xs])
                                                                 else Right (v, b'' ++ excluded)))

-- Restricts the assumptions for the purposes of the subcomputation.

withOnly :: (Prop -> Bool) -> Check t -> Check t
withOnly p c = Check (\b -> let (included, excluded) = partition (p . snd) b
                            in  case runCheck c included of
                                  (t, Left err) -> (t, Left err)
                                  (t, Right (v, b')) -> (t, Right (v, b' ++ excluded)))

-- Performs two subcomputations with the same assumptions; insists that the
-- unused bindings from each match.  This could be generalized to combine the
-- results of the two subcomputations; however, for the moment, it's sufficient
-- to restrict to () with the obvious combination.

andAlso :: Check () -> Check () -> Check ()
andAlso c c' =
    Check (\b -> case (runCheck c b, runCheck c' b) of
                   ((t, Left err), (t', _)) -> (t ++ t', Left err)
                   ((t, _), (t', Left err)) -> (t ++ t', Left err)
                   ((t, Right (_, b)), (t', Right (_, b')))
                       | same (filterNonlinear b) (filterNonlinear b') -> (t ++ t', Right ((), b))
                       | otherwise -> (t ++ t',
                                       let leftOver = filter (`notElem` b') b ++ filter (`notElem` b) b'
                                       in  Left (unlines ("Failed to consume bindings:" :
                                                          ["    " ++ x ++ ": " ++ show (pretty t) | (x, t) <- leftOver]))))
    where domain = map fst
          equalAsSet xs ys = all (`elem` xs) ys && all (`elem` ys) xs
          getBinding x b = case partition ((x ==) . fst) b of
                             ([(_, t)], _) -> t
                             _                 -> error "getBinding"
          filterNonlinear = filter (not . isWhyNot . snd)
          same b b' = equalAsSet (domain b) (domain b') && and [getBinding x b == getBinding x b' | x <- domain b]

-- Checks that there are no remaining linear bindings in the assumptions.


empty :: Check ()
empty = Check (\b -> let (nlb, lb) = partition (isWhyNot . snd) b
                     in  if null lb
                         then ([], Right ((), b))
                         else ([], Left (unlines ("Failed to consume bindings:" : ["    " ++ x ++ ": " ++ show (pretty t) | (x, t) <- b]))))

-- Generates error message.

unexpectedType :: String -> Prop -> Proc -> Check ()
unexpectedType x c p = fail ("Unexpected type " ++ show (pretty c) ++ " for " ++ x ++ " in "  ++ show (pretty p))

--------------------------------------------------------------------------------
-- Prop-checking CP expressions; this is a straight-forward, and somewhat
-- tedious, transcription of the typing rules.
--------------------------------------------------------------------------------

check :: Proc -> Check ()
check p = check' p >> empty
    where check' (Link w x) =
              do a <- consume w
                 b <- consume x
                 if dual a == b
                 then return ()
                 else fail ("In " ++ show (pretty (Link w x)) ++ ": types aren't dual:\n    " ++ show (pretty a) ++ "\n    " ++ show (pretty b))
          check' (Cut x a p q) =
              do provide x a (check' p)
                 provide x (dual a) (check' q)
          check' (Out x y p q) =
              do c <- consume x
                 case c of
                   a `Times` b ->
                       do provide y a (check' p)
                          provide x b (check' q)
                   _ -> unexpectedType x c (Out x y p q)
          check' (In x y p) =
              do c <- consume x
                 case c of
                   a `Par` b ->
                       provide y a (provide x b (check' p))
                   _ -> unexpectedType x c (In x y p)
          check' (Select x l p) =
              do c <- consume x
                 case c of
                   Plus lts
                       | Just a <- lookup l lts -> provide x a (check' p)
                       | otherwise -> fail ("Sum " ++ show (pretty (Plus lts)) ++ " does not contain label " ++ l)
                   _ -> unexpectedType x c (Select x l p)
          check' (Case x (b:bs)) =
              do c <- consume x
                 case c of
                   With lts ->
                       foldl andAlso (checkBranch lts b) (map (checkBranch lts) bs)
                   _ -> unexpectedType x c (Case x (b:bs))
              where checkBranch lts (l, p)
                        | Just a <- lookup l lts = provide x a (check' p)
                        | otherwise = fail ("Choice " ++ show (pretty (With lts)) ++ " does not contain label " ++ l)
          check' (Unroll x p) =
              do c <- consume x
                 case c of
                   Mu v a -> provide x (inst v (Mu v a) a) (check' p)
                   _      -> unexpectedType x c (Unroll x p)
          check' (Roll x z a p q) =
              do c <- consume x
                 case c of
                   Nu v b ->
                       do provide z a (check' p)
                          withOnly (const False) (provide z (dual a) (provide x (inst v a b) (check' q)))
                   _ -> unexpectedType x c (Roll x z a p q)
          check' (Replicate x y p) =
              do c <- consume x
                 case c of
                   OfCourse a ->
                       withOnly isWhyNot (provide y a (check' p))
                   _ -> unexpectedType x c (Replicate x y p)
          check' (Derelict x y p) =
              do c <- consume x
                 case c of
                   WhyNot a ->
                       provide y a (check' p)
                   _ -> unexpectedType x c (Derelict x y p)
          check' (SendProp x a p) =
              do c <- consume x
                 case c of
                   Exists z b ->
                       provide x (inst z a b) (check' p)
                   _ -> unexpectedType x c (SendProp x a p)
          check' (ReceiveProp x a p) =
              do c <- consume x
                 case c of
                   ForAll a' b | a == a' -> withOnly ((a `notElem`) . ftv) (provide x b (check' p))
                   _ -> unexpectedType x c (ReceiveProp x a p)
          check' (EmptyOut x) =
              do c <- consume x
                 case c of
                   One -> return ()
                   _   -> unexpectedType x c (EmptyOut x)
          check' (EmptyIn x p) =
              do c <- consume x
                 case c of
                   Bottom -> check' p
                   _      -> unexpectedType x c (EmptyIn x p)
          check' (EmptyCase x ys) =
              do c <- consume x
                 case c of
                   With [] -> mapM_ consume ys
                   _       -> unexpectedType x c (EmptyCase x ys)
          check' (Unk ys) =
              Check (\b -> ([filter ((`elem` ys) . fst) b], Right ((), (filter ((`notElem` ys) . fst) b))))
