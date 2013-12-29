{-# LANGUAGE TupleSections, PatternGuards #-}
module CP.Norm where

import Control.Monad.Error
import CP.Check
import Data.List (intercalate, nub, partition, tails)
import Data.Maybe
import CP.Syntax
import CP.Printer
import Text.PrettyPrint.Leijen

import Debug.Trace
--trace s x = x
showCP c = displayS (renderPretty 0.8 120 (pretty c)) ""

--------------------------------------------------------------------------------
-- Operators (types with holes)

type Op = (String, Prop)

appl :: Op -> Prop -> Prop
appl (x, b) a = inst x a b

dualOp :: Op -> Op
dualOp (x, b) = (x, dual (appl (x, b) (Neg x)))

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

data Fragment = Fragment [(String, Prop)] Proc

instance Pretty Fragment
    where pretty (Fragment zs p) = group (hang 2 (text "<" <> cat (punctuate (comma <> space) [text z <> colon <+> pretty a | (z,a) <- zs]) <> text ">" <$> pretty p))

addVar :: String -> Prop -> [Fragment] -> [Fragment]
addVar v a = concatMap add
    where add (Fragment vs p)
              | v `elem` fn p = fragment ((v, a) : vs') p
              | otherwise     = fragment vs p
              where vs' = filter ((v /=) . fst) vs

renameBoundVariable :: String -> Proc -> String -> Proc -> M (String, Proc, Proc)
renameBoundVariable x p x' p'
    | x == x' = return (x, p, p')
    | x `notElem` fn p' = liftM (x, p,) (replace x' x p')
    | x' `notElem` fn p = liftM (x',, p') (replace x x' p)
    | otherwise = do n <- fresh x
                     liftM2 (n,,) (replace x n p) (replace x' n p')

stepPrincipal :: Fragment -> Fragment -> M [Fragment]
stepPrincipal (Fragment zs (Link x y)) (Fragment zs' p)
    | x `elem` map fst zs', Just a <- lookup x zs, not (isWhyNot a) =
        do p' <- replace x y p
           return (fragment (add y zs') p')
    | y `elem` map fst zs', Just a <- lookup y zs, not (isWhyNot a) =
        do p' <- replace y x p
           return (fragment (add x zs') p')
    where isWhyNot WhyNot{} = True
          isWhyNot _        = False
          add z = case lookup z zs of
                    Nothing -> id
                    Just a  -> ((z, a) :)
stepPrincipal (Fragment zs (Out x y p q)) (Fragment zs' (In x' y' r))
    | x == x', Just (a `Times` b) <- lookup x zs =
        do (y'', p', r') <- renameBoundVariable y p y' r
           return (addVar y'' a (fragment zs p') ++
                   addVar y'' (dual a) (addVar x b (fragment zs q)) ++
                   addVar y'' (dual a) (addVar x (dual b) (fragment zs' r')))
stepPrincipal (Fragment zs (Select x l p)) (Fragment zs' (Case x' bs))
    | x == x', Just (Plus bts) <- lookup x zs, Just q <- lookup l bs, Just a <- lookup l bts =
        return (addVar x a (fragment zs p) ++
                addVar x (dual a) (fragment zs' q))
stepPrincipal (Fragment zs (SendProp x a p)) (Fragment zs' (ReceiveProp x' t' q))
    | x == x', Just (Exists t b) <- lookup x zs, t == t' =
        return (addVar x (inst t a b) (fragment [(z,inst t a c) | (z,c) <- zs] p) ++
                addVar x (dual (inst t a b)) (fragment [(z,inst t a c) | (z,c) <- zs'] (inst t a q)))
stepPrincipal (Fragment zs (EmptyOut x)) (Fragment zs' (EmptyIn x' p))
    | x == x', Just One <- lookup x zs =
        return (fragment (filter ((x' /=) . fst) zs') p)
stepPrincipal (Fragment zs (Unroll x p)) (Fragment zs' (Roll x' y s q r))
    | x == x', Just (Mu t a) <- lookup x zs =
        let b = (t, a)
            bbar = dualOp b
            nu (t, a) = Nu t a
        in  do z <- fresh "z"
               r' <- replace x z r
               recurse <- funct b x z (Roll z y s (Link x y) r')
               p' <- replace x z p
               if y `elem` fn p
               then do y' <- fresh y
                       q' <- replace y y' q
                       r' <- replace y y' r
                       return (addVar y' s (fragment zs' q') ++
                               addVar y' (dual s) (addVar x (bbar `appl` s) (fragment zs' r')) ++
                               addVar y' (dual s) (addVar x (dual (bbar `appl` s)) (addVar z (bbar `appl` nu bbar) (fragment zs' recurse))) ++
                               addVar y' (dual s) (addVar x (dual (bbar `appl` s)) (addVar z (dual (bbar `appl` nu bbar)) (fragment zs p'))))
               else return (addVar y s (fragment zs' q) ++
                            addVar y (dual s) (addVar x (bbar `appl` s) (fragment zs' r)) ++
                            addVar y (dual s) (addVar x (dual (bbar `appl` s)) (addVar z (bbar `appl` nu bbar) (fragment zs' recurse))) ++
                            addVar y (dual s) (addVar x (dual (bbar `appl` s)) (addVar z (dual (bbar `appl` nu bbar)) (fragment zs p'))))
    where -- assuming that there are propositions A and B such that q |- x:A,w:B,
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
stepPrincipal (Fragment zs (Replicate x y p)) (Fragment zs' (Derelict x' y' q))
    | x == x', Just (OfCourse a) <- lookup x zs =
        do (y'', p', q') <- renameBoundVariable y p y' q
           return (Fragment zs (Replicate x y p) :
                   addVar y'' a (fragment zs p') ++
                   addVar y'' (dual a) (fragment zs' q'))
stepPrincipal _ _ = return []

fragment :: [(String, Prop)] -> Proc -> [Fragment]
fragment zs (Cut x a p q) = fragment ((x,a) : zs) p ++ fragment ((x, dual a) : zs) q
fragment zs p             = [Fragment (filter ((`elem` vs) . fst) zs) p]
    where vs = fn p

unFragment :: [Fragment] -> Proc
unFragment fs = loop (filter (not . weaken) fs) []
    where weaken (Fragment _ p@(Replicate x _ _)) = and [x `notElem` map fst zs' | Fragment zs' p' <- fs, p /= p']
          weaken _                              = False

          loop [Fragment [] p] [] = p
          loop (Fragment [(x,a)] p : rest) passed = {- trace ("Introducing cut on " ++ x) $ -}
                                                    Cut x a p (loop (map filterX (rest ++ passed)) [])
              where filterX (Fragment zs q) = let f = Fragment (filter ((x /=) . fst) zs) q
                                              in  {- trace (unlines ["Filtered " ++ x ++ " from fragment", showCP (Fragment zs q), "Giving", showCP f]) -} f
          loop (f : rest) passed = loop rest (f : passed)
          loop [] passed = error (unlines ("Failed in unFragment! Remaining fragments were:" : map (showCP . pretty) passed))

commute :: [Fragment] -> ([Fragment] -> M Proc) -> ([Fragment] -> M Proc) -> M Proc
commute fs f g = loop fs [] False
    where loop pending passed = trace (unlines ("Commute pending" : map showCP pending ++ "Commute passed": map showCP passed)) (loop' pending passed)

          loop' [] passed True = f passed
          loop' [] passed False = g passed
          loop' (Fragment [] p : rest) passed b = loop' rest (Fragment [] p : passed) b
          loop' (Fragment zs (Out x y p q) : rest) passed _
              | x `notElem` map fst zs, not (null ps && null qs) =
                  trace (x ++ '[' : y ++ "]") $
                  do p' <- loop ps [] True
                     q' <- loop qs [] True
                     if null rest' then return (Out x y p' q') else loop rest' (fragment zs (Out x y p' q')) (p /= p' || q /= q')
              where pns = fn p
                    qns = fn q
                    pzs = filter (`elem` pns) (map fst zs)
                    qzs = filter (`elem` qns) (map fst zs)

                    part ps pzs qs qzs ss [] passed False
                        | null passed = (ps' ++ ss, qs' ++ ss, [])
                        | otherwise   = (ps' ++ ss, qs' ++ ss, passed ++ ss)
                        where pvs = concat [map fst vs | Fragment vs p <- passed]
                              ps' = [Fragment (filter ((`notElem` pvs) . fst) vs) p | Fragment vs p <- ps]
                              qs' = [Fragment (filter ((`notElem` pvs) . fst) vs) q | Fragment vs q <- qs]
                    part ps pzs qs qzs ss [] passed True = part ps pzs qs qzs ss passed [] False
                    part ps pzs qs qzs ss (Fragment zs (Replicate x y p) : rs) passed b = part ps pzs qs qzs (Fragment zs (Replicate x y p) : ss) rs passed b
                    part ps pzs qs qzs ss (Fragment zs r:rs) passed b
                        | any (`elem` pzs) (map fst zs) && all (`notElem` qzs) (map fst zs) = part (Fragment zs r : ps) (map fst zs ++ pzs) qs qzs ss rs passed True
                        | any (`elem` qzs) (map fst zs) && all (`notElem` pzs) (map fst zs) = part ps pzs (Fragment zs r : qs) (map fst zs ++ qzs) ss rs passed True
                        | otherwise = part ps pzs qs qzs rs ss (Fragment zs r : passed) b

                    (ps, qs, rest') = part (fragment zs p) pzs (fragment zs q) qzs [] (rest ++ passed) [] False

          loop' (Fragment zs (In x y p) : rest) passed _
              | x `notElem` map fst zs = trace (x ++ '(' : y ++ ")") $
                                         In x y `fmap` loop (fragment zs p ++ rest) passed True
          loop' (Fragment zs (Select x l p) : rest) passed _
              | x `notElem` map fst zs = trace (x ++ '/' : l) $
                                         Select x l `fmap` loop (fragment zs p ++ rest) passed True
          loop' (Fragment zs (Case x bs) : rest) passed _
              | x `notElem` map fst zs = trace ("case " ++ x) $
                                         Case x `fmap` sequence [(l,) `fmap` commute (fragment zs p ++ rest ++ passed) f g | (l,p) <- bs]
          loop' (Fragment zs (Unroll x p) : rest) passed _
              | x `notElem` map fst zs = trace ("unr " ++ x) $
                                         Unroll x `fmap` loop (fragment zs p ++ rest) passed True
          loop' (Fragment zs (Roll x y s p q) : rest) passed _
              | x `notElem` map fst zs = trace ("roll " ++ x ++ " [" ++ y ++ ": " ++ show (pretty s)) $
                                         flip (Roll x y s) q `fmap` loop (fragment zs p ++ rest) passed True
          loop' (Fragment zs (Replicate x y p) : rest) passed _
              | x `notElem` map fst zs, and [all (isWhyNot . snd) zs' | Fragment zs' _ <- rest ++ passed] =
                  Replicate x y `fmap` loop (fragment zs p ++ rest) passed True
              where isWhyNot (WhyNot _) = True
                    isWhyNot _          = False
          loop' (Fragment zs (Derelict x y p) : rest) passed _
              | x `notElem` map fst zs = trace ('?' : x ++ '[' : y ++ "]") $
                                         Derelict x y `fmap` loop (fragment zs p ++ rest) passed True
          loop' (Fragment zs (SendProp x a p) : rest) passed _
              | x `notElem` map fst zs = trace (x ++ "[" ++ show (pretty a) ++ "]") $
                                         SendProp x a `fmap` loop (fragment zs p ++ rest) passed True
          loop' (Fragment zs (ReceiveProp x t p) : rest) passed _
              | x `notElem` map fst zs = trace (x ++ "(" ++ t ++ ")") $
                                         ReceiveProp x t `fmap` loop (fragment zs p ++ rest) passed True
          loop' (Fragment zs (EmptyIn x p) : rest) passed _
              | x `notElem` map fst zs = trace (x ++ "()") $
                                         EmptyIn x `fmap` loop (fragment zs p ++ rest) passed True
          loop' (f : rest) passed b = loop rest (f : passed) b

normalize :: Proc -> M (Proc, Proc)
normalize p = trace ("Normalizing " ++ showCP p) $
              do let fs = fragment [] p
                     is = [1..length fs]
                     wl = makeWorkList is []
                 fs' <- loop wl (zip is fs) (length fs + 1)
                 executed <- commute fs' (return . unFragment) (return . unFragment)
                 simplified <- commute fs' recurse (return . unFragment)
                 return (executed, simplified)
    where recurse fs = trace (unlines ("Recursing on" : map showCP fs)) $
                       do fs' <- loop (makeWorkList is []) (zip is fs) (length fs + 1)
                          commute fs' recurse (return . unFragment)
              where is = [1..length fs]

          makeWorkList is js = [(i, i') | (i:is') <- tails is, i' <- is'] ++ [(i,j) | i <- is, j <- js]


          loop [] ifs _ = trace (unlines ("Done!" : map showCP  (map snd ifs))) $
                          return (map snd ifs)
          loop ((i,j):wl) ifs k
              | Just fi <- lookup i ifs, Just fj <- lookup j ifs =
                  trace (unlines ((show ((i,j):wl)) : map showCP (map snd ifs))) $
                  do fs' <- step fi fj
                     case fs' of
                       [] -> loop wl ifs k
                       _  -> let ks = [k..k + length fs' - 1]
                                 k' = k + length fs'
                                 notIorJ k = i /= k && j /= k
                                 ifs' = zip ks fs' ++ filter (notIorJ . fst) ifs
                                 wl'  = makeWorkList ks (filter notIorJ (map fst ifs)) ++
                                        [(i',j') | (i',j') <- wl, notIorJ i', notIorJ j']
                             in  loop wl' ifs' k'
              | otherwise = error "Missing fragments in loop"

          step fi fj =
              do fs <- stepPrincipal fi fj
                 case fs of
                   [] -> stepPrincipal fj fi
                   _  -> return fs
