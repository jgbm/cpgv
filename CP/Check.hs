module CP.Check where

import Control.Monad
import Control.Monad.State (evalStateT)
import Data.List
import CP.Expand (expandB)
import CP.Syntax
import CP.Printer

import Text.PrettyPrint.Leijen (renderPretty)

isWhyNot (WhyNot _) = True
isWhyNot _          = False

--------------------------------------------------------------------------------
-- Checking monad.  Each checking operation takes a list of assumptions as
-- arguments, and produces either an error message, or a (reduced) list of
-- arguments as a result.
--------------------------------------------------------------------------------

type Environment = [(String, FOType)]
newtype Check t = Check { runCheck :: (Behavior, Environment) -- initial context
                                   -> ([Behavior],            -- traced contexts
                                       Either String          -- typing failure
                                              (t, Behavior))  -- remaining context
                        }

instance Functor Check
    where fmap f (Check g) = Check (\b -> case g b of
                                            (t, Left err) -> (t, Left err)
                                            (t, Right (v, b')) -> (t, Right (f v, b')))

instance Monad Check
    where return v = Check (\(b, e) -> ([], Right (v, b)))
          Check f >>= g = Check (\(b, e) -> case f (b, e) of
                                              (t, Left err) -> (t, Left err)
                                              (t, Right (v, b')) ->
                                                 case runCheck (g v) (b', e) of
                                                   (t', Left err) -> (t ++ t', Left err)
                                                   (t', Right (v', b'')) -> (t ++ t', Right (v', b'')))
          fail s = Check (\_ -> ([], Left s))

-- Looks up the provided identifier in the assumptions, removing its typing from
-- the assumption list.

consume :: String -> Check Prop
consume x = Check (\(b, e) -> ([], case partition ((x ==) . fst) b of
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
provide x t c = Check (\(b, e) -> let (included, excluded) = partition ((x /=) . fst) b
                                  in  case runCheck c ((x, t) : included, e) of
                                        (t, Left err) -> (t, Left err)
                                        (t, Right (v, b')) -> (t, let (xs, b'') = partition ((x ==) . fst) b'
                                                                  in  if any (not . isWhyNot . snd) xs
                                                                      then Left ("Failed to consume bindings " ++ intercalate "," [x ++ ": " ++ show (pretty t) | (x, t) <- xs])
                                                                      else Right (v, b'' ++ excluded)))

-- Restricts the assumptions for the purposes of the subcomputation.

withOnly :: (Prop -> Bool) -> Check t -> Check t
withOnly p c = Check (\(b, e) -> let (included, excluded) = partition (p . snd) b
                                 in  case runCheck c (included, e) of
                                       (t, Left err) -> (t, Left err)
                                       (t, Right (v, b')) -> (t, Right (v, b' ++ excluded)))

-- Performs two subcomputations with the same assumptions; insists that the
-- unused bindings from each match.  This could be generalized to combine the
-- results of the two subcomputations; however, for the moment, it's sufficient
-- to restrict to () with the obvious combination.

andAlso :: Check () -> Check () -> Check ()
andAlso c c' =
    Check (\(b, e) -> case (runCheck c (b, e), runCheck c' (b, e)) of
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
empty = Check (\(b, _) -> let (nlb, lb) = partition (isWhyNot . snd) b
                          in  if null lb
                              then ([], Right ((), b))
                              else ([], Left (unlines ("Failed to consume bindings:" : ["    " ++ x ++ ": " ++ show (pretty t) | (x, t) <- b]))))

-- Generates error message.
unexpectedType :: String -> Prop -> Proc -> Check ()
unexpectedType x c p = fail ("Unexpected type " ++ show (pretty c) ++ " for " ++ x ++ " in "  ++ show (pretty p))

introduce v t c = Check (\(b, e) -> runCheck c (b, (v, t) : e))
typeOf v = Check (\(b, e) -> case lookup v e of
                               Nothing -> ([], Left ("Missing type for " ++ v))
                               Just t  -> ([], Right (t, b)))


--------------------------------------------------------------------------------
-- Type-checking CP expressions; this is a straight-forward, and somewhat
-- tedious, transcription of the typing rules.
--------------------------------------------------------------------------------

addError p c = Check (\e -> case runCheck c e of
                              (t, Left err)
                                  | '\n' `notElem` err -> (t, Left (err ++ "\n    while checking " ++ displayS (renderPretty 0.8 120 (pretty p)) ""))
                                  | otherwise -> (t, Left err)
                              (t, Right x) -> (t, Right x))

check :: Proc -> Check ()
check p = check' p >> empty
    where check' (Link w x) =
              addError (Link w x) $
              do a <- consume w
                 b <- consume x
                 if dual a == b
                 then return ()
                 else fail ("In " ++ show (pretty (Link w x)) ++ ": types aren't dual:\n    " ++ show (pretty a) ++ "\n    " ++ show (pretty b))
          check' (Cut x a p q) =
              addError (Cut x a p q) $
              do provide x a (check' p)
                 provide x (dual a) (check' q)
          check' (Out x y p q) =
              addError (Out x y p q) $
              do c <- consume x
                 case c of
                   a `Times` b ->
                       do provide y a (check' p)
                          provide x b (check' q)
                   _ -> unexpectedType x c (Out x y p q)
          check' (In x y p) =
              addError (In x y p) $
              do c <- consume x
                 case c of
                   a `Par` b ->
                       provide y a (provide x b (check' p))
                   _ -> unexpectedType x c (In x y p)
          check' (Select x l p) =
              addError (Select x l p) $
              do c <- consume x
                 case c of
                   Plus lts
                       | Just a <- lookup l lts -> provide x a (check' p)
                       | otherwise -> fail ("Sum " ++ show (pretty (Plus lts)) ++ " does not contain label " ++ l)
                   _ -> unexpectedType x c (Select x l p)
          check' (Case x (b:bs)) =
              addError (Case x (b:bs)) $
              do c <- consume x
                 case c of
                   With lts ->
                       foldl andAlso (checkBranch lts b) (map (checkBranch lts) bs)
                   _ -> unexpectedType x c (Case x (b:bs))
              where checkBranch lts (l, p)
                        | Just a <- lookup l lts = provide x a (check' p)
                        | otherwise = fail ("Choice " ++ show (pretty (With lts)) ++ " does not contain label " ++ l)
          check' (Unroll x p) =
              addError (Unroll x p) $
              do c <- consume x
                 case c of
                   Mu v a -> provide x (inst v (Mu v a) a) (check' p)
                   _      -> unexpectedType x c (Unroll x p)
          check' (Roll x z a p q) =
              addError (Roll x z a p q) $
              do c <- consume x
                 case c of
                   Nu v b ->
                       do provide z a (check' p)
                          withOnly (const False) (provide z (dual a) (provide x (inst v a b) (check' q)))
                   _ -> unexpectedType x c (Roll x z a p q)
          check' (Replicate x y p) =
              addError (Replicate x y p) $
              do c <- consume x
                 case c of
                   OfCourse a ->
                       withOnly isWhyNot (provide y a (check' p))
                   _ -> unexpectedType x c (Replicate x y p)
          check' (Derelict x y p) =
              addError (Derelict x y p) $
              do c <- consume x
                 case c of
                   WhyNot a ->
                       provide y a (check' p)
                   _ -> unexpectedType x c (Derelict x y p)
          check' (SendProp x a p) =
              addError (SendProp x a p) $
              do c <- consume x
                 case c of
                   Exist z b ->
                       provide x (inst z a b) (check' p)
                   _ -> unexpectedType x c (SendProp x a p)
          check' (ReceiveProp x a p) =
              addError (ReceiveProp x a p) $
              do c <- consume x
                 case c of
                   Univ a' b | a == a' -> withOnly ((a `notElem`) . fpv) (provide x b (check' p))
                   _ -> unexpectedType x c (ReceiveProp x a p)
          check' (SendTerm x m p) =
              addError (SendTerm x m p) $
              do c <- consume x
                 case c of
                   FOExist t a -> do t' <- focheck m
                                     when (t /= t') (fail ("Expected type " ++ show (pretty t) ++ " for " ++ show (pretty m)))
                                     provide x a (check' p)
                   _           -> unexpectedType x c (SendTerm x m p)
          check' (ReceiveTerm x i p) =
              addError (ReceiveTerm x i p) $
              do c <- consume x
                 case c of
                   FOUniv t a -> introduce i t (provide x a (check' p))
                   _          -> unexpectedType x c (ReceiveTerm x i p)
          check' (EmptyOut x) =
              addError (EmptyOut x) $
              do c <- consume x
                 case c of
                   One -> return ()
                   _   -> unexpectedType x c (EmptyOut x)
          check' (EmptyIn x p) =
              addError (EmptyIn x p) $
              do c <- consume x
                 case c of
                   Bottom -> check' p
                   _      -> unexpectedType x c (EmptyIn x p)
          check' (EmptyCase x ys) =
              addError (EmptyCase x ys) $
              do c <- consume x
                 case c of
                   With [] -> mapM_ consume ys
                   _       -> unexpectedType x c (EmptyCase x ys)
          check' (Quote m (Just ds)) =
              do t <- focheck m
                 case t of
                   TQuote b -> mapM_ checkVar (runM (expandB ds b))
                   _ -> fail ("Quoted expression " ++ show (pretty m) ++ " does not have behavior type")
              where runM c = case evalStateT (unM c) 0 of
                               Left err -> error err
                               Right t  -> t
                    checkVar (v, t) =
                        addError ("the binding " ++ v ++ ": " ++ show (pretty t)) $
                        do t' <- consume v
                           when (t /= t') (fail ("Expected channel " ++ v ++ " to have type " ++ show (pretty t) ++ ", not " ++ show (pretty t')))
          check' (Unk []) =
              Check (\(b, _) -> ([b], Right ((), filter (isWhyNot . snd) b)))
          check' (Unk ys) =
              Check (\(b, _) -> ([filter ((`elem` ys) . fst) b], Right ((), [(x,t) | (x,t) <- b, x `notElem` ys || isWhyNot t])))

focheck :: FOTerm -> Check FOType
focheck (EVar s)
    | s == "+" || s == "*" = return (Int `To` (Int `To` Int))
    | s == "isZero" = return (Int `To` Bool)
    | otherwise = typeOf s
focheck (EInt _) = return Int
focheck (EBool _) = return Bool
focheck EUnit = return Unit
focheck (EApp m n) =
    do t <- focheck m
       u <- focheck n
       case t of
         u' `To` v
             | u == u' -> return v
             | otherwise -> fail ("Argument type " ++ show (pretty u) ++ " does not match expected " ++ show (pretty u') ++ " in application " ++ show (pretty (EApp m n)))
         _ -> fail ("Non-function type " ++ show (pretty t) ++ " in application " ++ show (pretty (EApp m n)))
focheck (EFix e) =
    do t <- focheck e
       case t of
         u `To` v | u == v -> return v
         _ -> fail ("Unexpected argument " ++ show (pretty e) ++ " to fix of type " ++ show (pretty t))
focheck (EIf m n o) =
    do tm <- focheck m
       tn <- focheck n
       to <- focheck o
       when (tm /= Bool) (fail ("Condition does not have boolean type: " ++ show (pretty (EIf m n o))))
       when (tn /= to)   (fail ("Branches have disparate types " ++ show (pretty tn) ++ " and " ++ show (pretty to) ++ " in conditional " ++ show (pretty (EIf m n o))))
       return tn
focheck (ELam x t m) = liftM (t `To`) (introduce x t (focheck m))
focheck (EQuote p b) = Check (\(b', e) -> case runCheck (check p) (b, e) of
                                            (t, Right ((), _)) -> (t, Right (TQuote b, b'))
                                            (t, Left err) -> (t, Left err))
