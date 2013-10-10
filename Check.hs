module Check where

import Data.List
import Syntax.AbsCP
import Syntax.PrintCP

--------------------------------------------------------------------------------
-- Utility operations on types
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Negating types
dual :: Type -> Type
-- Variables
dual (Var s) = Neg s
dual (Neg s) = Var s
-- Multiplicative combinators
dual (a `Times` b) = dual a `Par` dual b
dual (a `Par` b) = dual a `Times` dual b
dual One = Bottom
dual Bottom = One
-- Additive combinators
dual (a `Plus` b) = dual a `With` dual b
dual (a `With` b) = dual a `Plus` dual b
dual Zero = Top
dual Top = Zero
-- Exponentials
dual (OfCourse a) = WhyNot (dual a)
dual (WhyNot a) = OfCourse (dual a)
-- Quantifiers
dual (ForAll x a) = Exists x (dual a)
dual (Exists x a) = ForAll x (dual a)
-- Oops
dual t            = error ("Encountered " ++ printTree t ++ " in dual.")

--------------------------------------------------------------------------------
-- Free type variables
ftv :: Type -> [UIdent]
-- Variables
ftv (Var s) = [s]
ftv (Neg s) = [s]
-- Multiplicative combinators
ftv (a `Times` b) = concatMap ftv [a,b]
ftv (a `Par` b) = concatMap ftv [a,b]
ftv One = []
ftv Bottom = []
-- Additive combinators
ftv (a `Plus` b) = concatMap ftv [a,b]
ftv (a `With` b) = concatMap ftv [a,b]
ftv Zero = []
ftv Top = []
-- Exponentials
ftv (OfCourse a) = ftv a
ftv (WhyNot a) = ftv a
-- Quantifiers
ftv (ForAll x a) = filter (x /=) (ftv a)
ftv (Exists x a) = filter (x /=) (ftv a)

--------------------------------------------------------------------------------
-- Instantiating type variables
class HasTyVars t
    where inst :: UIdent -> Type -> t -> t

instance HasTyVars Type
    where -- Variables
          inst x c (Var x') | x == x' = c
                            | otherwise = Var x'
          inst x c (Neg x') | x == x' = dual c
                            | otherwise = Neg x'
          -- Multiplicative combinators
          inst x c (a `Times` b) = inst x c a `Times` inst x c b
          inst x c (a `Par` b) = inst x c a `Par` inst x c b
          inst _ _ One = One
          inst _ _ Bottom = Bottom
          -- Additive combinators
          inst x c (a `Plus` b) = inst x c a `Plus` inst x c b
          inst x c (a `With` b) = inst x c a `With` inst x c b
          inst x c Zero = Zero
          inst x c Top = Top
          -- Exponentials
          inst x c (OfCourse a) = OfCourse (inst x c a)
          inst x c (WhyNot a) = WhyNot (inst x c a)
          -- Quantifiers
          inst x c (ForAll x' a) | x == x' = ForAll x' a
                                 | otherwise = ForAll x' (inst x c a)
          inst x c (Exists x' a) | x == x' = Exists x' a
                                 | otherwise = Exists x' (inst x c a)

--------------------------------------------------------------------------------
-- Checking monad.  Each checking operation takes a list of assumptions as
-- arguments, and produces either an error message, or a (reduced) list of
-- arguments as a result.
--------------------------------------------------------------------------------

type Behavior = [Typing]
newtype Check t = Check { runCheck :: Behavior {- initial context -}
                                   -> Either String {- typing failure -}
                                             (t, Behavior) {- remaining context -}
                        }

instance Functor Check
    where fmap f (Check g) = Check (\b -> case g b of
                                            Left err -> Left err
                                            Right (v, b') -> Right (f v, b'))

instance Monad Check
    where return v = Check (\b -> Right (v, b))
          Check f >>= g = Check (\b -> case f b of
                                         Left err -> Left err
                                         Right (v, b') -> runCheck (g v) b')
          fail s = Check (\_ -> Left s)

name :: Typing -> LIdent
name (Typing id _) = id

typ :: Typing -> Type
typ (Typing _ t) = t

-- Looks up the provided identifier in the assumptions, removing its typing from
-- the assumption list.

consume :: LIdent -> Check Type
consume x = Check (\b -> case partition ((x ==) . name) b of
                           ([], _) -> Left ("No type for " ++ printTree x)
                           ([Typing _ t], b') -> Right (t, b')
                           _ -> error ("Internal failure: multiple bindings of " ++ printTree x ++ " in behavior."))

-- Adds a binding to the assumption list for the purposes of the subcomputation.
-- Two wrinkles:
--  - We insist that, unless the binding has a why-not typing, the binding is
--    used during the subcomputation.
--  - Should the new binding shadow an existing binding, that binding is removed
--    from the assumptions for the purposes of the subcomputation, and
--    reintroduced in the result of provide.

provide :: LIdent -> Type -> Check t -> Check t
provide x t c = Check (\b -> let (included, excluded) = partition ((x /=) . name) b
                             in  case runCheck c (Typing x t : included) of
                                   Left err -> Left err
                                   Right (v, b') ->
                                        if any ((x ==) . name) b' && not (isWhyNot t)
                                        then Left ("Failed to consume binding " ++ printTree x ++ ": " ++ printTree t)
                                        else Right (v, b' ++ excluded))


-- Restricts the assumptions for the purposes of the subcomputation.

withOnly :: (Type -> Bool) -> Check t -> Check t
withOnly p c = Check (\b -> let (included, excluded) = partition (p . typ) b
                            in  case runCheck c included of
                                  Left err -> Left err
                                  Right (v, b') -> Right (v, b' ++ excluded))

-- Performs two subcomputations with the same assumptions; insists that the
-- unused bindings from each match.  This could be generalized to combine the
-- results of the two subcomputations; however, for the moment, it's sufficient
-- to restrict to () with the obvious combination.

andAlso :: Check () -> Check () -> Check ()
andAlso c c' =
    Check (\b -> case (runCheck c b, runCheck c' b) of
                   (Left err, _) -> Left err
                   (_, Left err) -> Left err
                   (Right (_, b), Right (_, b'))
                       | same b b' -> Right ((), b)
                       | otherwise -> let leftOver = filter (`notElem` b') b ++ filter (`notElem` b) b'
                                      in  Left (unlines ("Failed to consume bindings:" :
                                                         ["    " ++ printTree x ++ ": " ++ printTree t | Typing x t <- leftOver])))
    where domain = map name
          equalAsSet xs ys = all (`elem` xs) ys && all (`elem` ys) xs
          getBinding x b = case partition ((x ==) . name) b of
                             ([Typing _ t], _) -> t
                             _                 -> error "getBinding"
          same b b' = equalAsSet (domain b) (domain b') && and [getBinding x b == getBinding x b' | x <- domain b]

isWhyNot (WhyNot _) = True
isWhyNot _          = False

-- Checks that there are no remaining linear bindings in the assumptions.

empty :: Check ()
empty = Check (\b -> let (nlb, lb) = partition (isWhyNot . typ) b
                     in  if null lb
                         then Right ((), b)
                         else Left (unlines ("Failed to consume bindings:" : ["    " ++ printTree x ++ ": " ++ printTree t | Typing x t <- b])))

-- Generates error message.

unexpectedType :: LIdent -> Type -> Proc -> Check ()
unexpectedType x c p = fail ("Unexpected type " ++ printTree c ++ " for " ++ printTree x ++ " in "  ++ printTree p)

--------------------------------------------------------------------------------
-- Type-checking CP expressions; this is a straight-forward, and somewhat
-- tedious, transcription of the typing rules.
--------------------------------------------------------------------------------

check :: Proc -> Check ()
check p = check' p >> empty
    where check' (Link w x) =
              do a <- consume w
                 b <- consume x
                 if dual a == b
                 then return ()
                 else fail ("In " ++ printTree (Link w x) ++ ": types aren't dual:\n    " ++ printTree a ++ "\n    " ++ printTree b)
          check' (Comp x a p q) =
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
          check' (Inl x p) =
              do c <- consume x
                 case c of
                   a `Plus` b ->
                       provide x a (check' p)
                   _ -> unexpectedType x c (Inl x p)
          check' (Inr x p) =
              do c <- consume x
                 case c of
                   a `Plus` b ->
                       provide x b (check' p)
                   _ -> unexpectedType x c (Inr x p)
          check' (Case x p q) =
              do c <- consume x
                 case c of
                   a `With` b ->
                       provide x a (check' p) `andAlso`
                       provide x b (check' q)
                   _ -> unexpectedType x c (Case x p q)
          check' (ServerAccept x y p) =
              do c <- consume x
                 case c of
                   OfCourse a ->
                       withOnly isWhyNot (provide y a (check' p))
                   _ -> unexpectedType x c (ServerAccept x y p)
          check' (ClientRequest x y p) =
              do c <- consume x
                 case c of
                   WhyNot a ->
                       provide x (WhyNot a) (provide y a (check' p))
          check' (SendType x a p) =
              do c <- consume x
                 case c of
                   Exists z b ->
                       provide x (inst z a b) (check' p)
                   _ -> unexpectedType x c (SendType x a p)
          check' (ReceiveType x a p) =
              do c <- consume x
                 case c of
                   ForAll a' b | a == a' -> withOnly ((a `notElem`) . ftv) (provide x b (check' p))
                   _ -> unexpectedType x c (ReceiveType x a p)
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
                   Top -> mapM_ consume ys
                   _   -> unexpectedType x c (EmptyCase x ys)
