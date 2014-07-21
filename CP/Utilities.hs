module CP.Utilities where

import Control.Monad
import CP.Syntax

binderClash :: Proc -> Maybe String
binderClash p = descend [] p
    where descend _ ProcVar{} = Nothing
          descend _ Link{} = Nothing
          descend bs (Cut x _ p q)
              | x `elem` bs = Just x
              | otherwise   = msum [descend (x:bs) p, descend (x:bs) q]
          descend bs (Out _ x p q)
              | x `elem` bs = Just x
              | otherwise = msum [descend (x:bs) p, descend bs q]
          descend bs (In _ y p)
              | y `elem` bs = Just y
              | otherwise = descend (y:bs) p
          descend bs (Select _ _ p) = descend bs p
          descend bs (Case _ branches) = msum (map (descend bs . snd) branches)
          descend bs (Rec _ p) = descend bs p
          descend bs (CoRec _ y _ p q)
              | y `elem` bs = Just y
              | otherwise = msum [descend (y:bs) p, descend (y:bs) q]
          descend bs (Replicate _ y p)
              | y `elem` bs = Just y
              | otherwise = descend (y:bs) p
          descend bs (Derelict _ y p)
              | y `elem` bs = Just y
              | otherwise = descend (y:bs) p
          descend bs (SendProp _ _ p) = descend bs p
          descend bs (ReceiveProp _ _ p) = descend bs p
          descend bs (SendTerm _ _ p) = descend bs p
          descend bs (ReceiveTerm _ y p)
              | y `elem` bs = Just y
              | otherwise = descend (y:bs) p
          descend _ EmptyOut{} = Nothing
          descend bs (EmptyIn _ p) = descend bs p
          descend _ EmptyCase{} = Nothing
          descend _ Quote{} = Nothing
          descend _ Unk{} = Nothing
