module EvalGV where

import Syntax.AbsGV
import Syntax.PrintGV

import Control.Monad
import Data.Maybe

data Value =
   VUnit
 | VFun Var Term
 | VPair Value Value
 | VLabel Label
 | VChannel Chan
   deriving (Eq,Ord,Show)

-- valueToTerm :: Value -> Term
-- valueToTerm VUnit        = Unit
-- valueToTerm (VFun x e)   = Fun x e
-- valueToTerm (VPair v w)  = Pair (valueToTerm v) (valueToTerm w)
-- valueToTerm (VChannel c) = undefined

-- runtime channels
type Port = Int
type Chan = (Port, Port)

type Var = LIdent
type Label = LIdent

type Buffer = (Port, [Value])
type Env k v = [(k, v)]
type VEnv = Env Var Value

type Configuration = ([Buffer], [Susp Value], Port)

-- a possibly suspended value
data Susp a =
   Return a
 | SWith (Chan -> (Susp Value, Susp Value)) (Value -> Susp a)
 | SSend Value Chan (Value -> Susp a)
 | SReceive Chan (Value -> Susp a)
 | SSelect Label Chan (Value -> Susp a)
 | SCase Chan (Env Label (Value -> Susp Value)) (Value -> Susp a)

instance Monad Susp where
  return = Return
  Return v       >>= k = k v  
  SWith f k'     >>= k = SWith f     (k' >=> k)
  SSend v c k'   >>= k = SSend v c   (k' >=> k)
  SReceive c k'  >>= k = SReceive c  (k' >=> k)
  SSelect l c k' >>= k = SSelect l c (k' >=> k)
  SCase c bs k'  >>= k = SCase c bs  (k' >=> k)

swith f     = SWith f return
ssend v c   = SSend v c return
sreceive c  = SReceive c return
sselect l c = SSelect l c return
scase v bs  = SCase v bs return

extend = flip (:)

-- evaluate as much as possible in a single thread
evalThread :: VEnv -> Term -> Susp Value
evalThread env e = evalThread' env e where
  et = evalThread env
  evalThread' env (Var x)   =
    case lookup x env of
      Nothing -> error ("Unbound variable: " ++ show x)
      Just v -> return v
  evalThread' env Unit = return VUnit
  evalThread' env (LinLam x _ e) = return (VFun x e)
  evalThread' env (UnlLam x _ e) = return (VFun x e)
  evalThread' env (App f a) =
    do VFun x e <- et f
       v <- et a
       evalThread (extend env (x, v)) e
  evalThread' env (Pair e1 e2) =
    do v1 <- et e1
       v2 <- et e2
       return (VPair v1 v2)
  evalThread' env (Let (BindName x) e e') =
    do v <- et e
       evalThread (extend env (x, v)) e'
  evalThread' env (Let (BindPair x1 x2) e e') =
    do (VPair v1 v2) <- et e
       evalThread (extend (extend env (x1, v1)) (x2, v2)) e'
  evalThread' env (With x _ e1 e2) =
    swith (\(c1, c2) -> (evalThread (extend env (x, VChannel (c1, c2))) e1,
                         evalThread (extend env (x, VChannel (c2, c1))) e2))
  evalThread' env (End e) = et e
  evalThread' env (Send m n) =
    do v <- et m
       (VChannel c) <- et n
       ssend v c
  evalThread' env (Receive e) =
    do (VChannel c) <- et e
       sreceive c
  evalThread' env (Select l e) =
    do (VChannel c) <- et e
       sselect l c
  evalThread' env (Case e bs) =
    do (VChannel c) <- et e
       let bs' = map (\(Branch l x e) -> (l, \v -> evalThread (extend env (x, v)) e)) bs
       scase c bs'

-- perform up to one concurrency step
step :: Susp Value -> [Buffer] -> [Susp Value] -> Port -> Maybe Configuration
step (Return _) _ _ _ = Nothing
step (SWith f k) cs ts next = Just ((next+1, []):(next, []):cs, ts ++ [t1, t2 >>= k], next+2)
  where
    (t1, t2) = f (next, next+1)
step (SSend v c k) cs ts next = Just (sendValue v c cs, ts ++ [k (VChannel c)], next)
step (SReceive c k) cs ts next =
  do (v, cs') <- receiveValue c cs 
     return (cs', ts ++ [k (VPair v (VChannel c))], next)  
step (SSelect l c k) cs ts next = Just (sendLabel l c cs, ts ++ [k (VChannel c)], next)
step (SCase c bs k) cs ts next =
  do (s, cs') <- receiveLabel c bs cs 
     return (cs', ts ++ [s >>= k], next)

sendValue :: Value -> Chan -> [Buffer] -> [Buffer]
sendValue v (p, _) = map (\(q, vs) -> if p == q then (q, vs ++ [v])
                                      else (q, vs))

receiveValue :: Chan -> [Buffer] -> Maybe (Value, [Buffer])
receiveValue (_, p) ((q, []):cs) | p == q = Nothing
receiveValue (_, p) ((q, v:vs):cs) | p == q = Just (v, (q, vs):cs)
receiveValue c      (c':cs) =
  do (v, cs') <- receiveValue c cs
     return (v, c':cs')

sendLabel :: Label -> Chan -> [Buffer] -> [Buffer]
sendLabel l (p, _) = map (\(q, vs) -> if p == q then (q, vs ++ [VLabel l])
                                        else (q, vs))

receiveLabel :: Chan -> Env Label (Value -> Susp Value) -> [Buffer] -> Maybe (Susp Value, [Buffer])
receiveLabel c@(_, p) bs ((q, []):cs) | p == q = Nothing
receiveLabel c@(_, p) bs ((q, (VLabel l):vs):cs) | p == q =
  do v <- matchLabel c l bs
     return (v, (q, vs):cs)
  where
    matchLabel c l bs =
      do f <- lookup l bs
         return $ f (VChannel c)
receiveLabel c        bs (c':cs) =
  do (t, cs') <- receiveLabel c bs cs
     return (t, c':cs')

evalConfig :: Configuration -> [Susp Value]
evalConfig conf = evalConfig' 0 conf
  where
    -- keep going until all threads are blocked
    evalConfig' :: Int -> Configuration -> [Susp Value]
    evalConfig' n (cs, ts, next) | n >= length ts = ts
    evalConfig' n (cs, t:ts, next) =
      case step t cs ts next of
        Nothing -> evalConfig' (n+1) (cs, ts ++ [t], next)
        Just conf -> evalConfig conf

evalProgram :: Term -> Value
evalProgram e = case last (evalConfig ([], [evalThread [] e], 0)) of
                  Return v -> v
