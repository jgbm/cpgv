module RunGV where

import Syntax.AbsGV
import Syntax.PrintGV

import Control.Monad
import Control.Monad.Error
import Data.Maybe

data Value =
   VUnit
 | VFun Var Term
 | VPair Value Value
 | VLabel Label
 | VChannel Chan
   deriving (Eq,Ord,Show)

-- runtime channels
type Port = Int
type Chan = (Port, Port)

type Var = LIdent
type Label = LIdent

type Buffer = (Port, [Value], Maybe Port)
type Env k v = [(k, v)]
type VEnv = Env Var Value

type Configuration = ([Buffer], [Thread], Port)

-- a possibly suspended value
--
-- We always instantiate the parameter to the type Value. The
-- parameter is only there to allow us to declare Susp to be a monad
-- and hence use do notation!
data Susp a =
   Return a
 | SExit Value
 | SWith (Chan -> (Thread, Thread)) (Value -> Susp a)
 | SLink Chan Chan (Value -> Susp a)
 | SSend Value Chan (Value -> Susp a)
 | SReceive Chan (Value -> Susp a)
 | SSelect Label Chan (Value -> Susp a)
 | SCase Chan (Env Label (Value -> Thread)) (Value -> Susp a)

type Thread = Susp Value

instance Monad Susp where
  return = Return
  Return v       >>= k = k v
  SExit v        >>= k = SExit v
  SWith f k'     >>= k = SWith f     (k' >=> k)
  SLink c1 c2 k' >>= k = SLink c1 c2 (k' >=> k)
  SSend v c k'   >>= k = SSend v c   (k' >=> k)
  SReceive c k'  >>= k = SReceive c  (k' >=> k)
  SSelect l c k' >>= k = SSelect l c (k' >=> k)
  SCase c bs k'  >>= k = SCase c bs  (k' >=> k)

sexit       = SExit
swith f     = SWith f return
slink c1 c2 = SLink c1 c2 return
ssend v c   = SSend v c return
sreceive c  = SReceive c return
sselect l c = SSelect l c return
scase v bs  = SCase v bs return

extend = flip (:)

-- run as much pure computation as possible in a single thread
runPure :: VEnv -> Term -> Thread
runPure env e = runPure' env e where
  rp = runPure env
  runPure' env (Var x)   =
    case lookup x env of
      Nothing -> error ("Unbound variable: " ++ show x)
      Just v -> return v
  runPure' env Unit = return VUnit
  runPure' env (Link e1 e2) =
    do (VChannel c1) <- rp e1
       (VChannel c2) <- rp e2
       slink c1 c2
  runPure' env (LinLam x _ e) = return (VFun x e)
  runPure' env (UnlLam x _ e) = return (VFun x e)
  runPure' env (App f a) =
    do VFun x e <- rp f
       v <- rp a
       runPure (extend env (x, v)) e
  runPure' env (Pair e1 e2) =
    do v1 <- rp e1
       v2 <- rp e2
       return (VPair v1 v2)
  runPure' env (Let (BindName x) e e') =
    do v <- rp e
       runPure (extend env (x, v)) e'
  runPure' env (Let (BindPair x1 x2) e e') =
    do (VPair v1 v2) <- rp e
       runPure (extend (extend env (x1, v1)) (x2, v2)) e'
  runPure' env (With x _ e1 e2) =
    swith (\(c1, c2) -> (runPure (extend env (x, VChannel (c1, c2))) e1,
                         runPure (extend env (x, VChannel (c2, c1))) e2))
  runPure' env (End e) = rp e
  runPure' env (Send m n) =
    do v <- rp m
       (VChannel c) <- rp n
       ssend v c
  runPure' env (Receive e) =
    do (VChannel c) <- rp e
       sreceive c
  runPure' env (Select l e) =
    do (VChannel c) <- rp e
       sselect l c
  runPure' env (Case e bs) =
    do (VChannel c) <- rp e
       let bs' = map (\(Branch l x e) -> (l, \v -> runPure (extend env (x, v)) e)) bs
       scase c bs'

blocked = Left Nothing
exit v = Left (Just v)

emptyBuffer :: Port -> Buffer
emptyBuffer p = (p, [], Nothing)

-- run the next command in the current thread
runCommand :: Thread -> [Buffer] -> [Thread] -> Port -> Either (Maybe Value) Configuration
runCommand (Return _) _ _ _ = blocked -- this is actually a finished thread rather than a blocked thread
runCommand (SExit v) _ _ _ = exit v
runCommand (SWith f k) cs ts next = return ((emptyBuffer (next+1)):(emptyBuffer next):cs, ts ++ [t1, t2 >>= k], next+2) where
  (t1, t2) = f (next, next+1)
runCommand (SLink c1 c2 k) cs ts next = return (linkChannels c1 c2 cs, ts ++ [k (VChannel c1)], next)
runCommand (SSend v c k) cs ts next = return (sendValue v c cs, ts ++ [k (VChannel c)], next)
runCommand (SReceive c k) cs ts next =
  do (v, cs') <- receiveValue c cs 
     return (cs', ts ++ [k (VPair v (VChannel c))], next)  
runCommand (SSelect l c k) cs ts next = return (sendLabel l c cs, ts ++ [k (VChannel c)], next)
runCommand (SCase c bs k) cs ts next =
  do (s, cs') <- receiveLabel c bs cs 
     return (cs', ts ++ [s >>= k], next)

linkChannels :: Chan -> Chan -> [Buffer] -> [Buffer]
linkChannels (p1, q1) (p2, q2) cs = map (\(p, vs, f) ->
  if      p == p1 then (p1, vs, Just p2)
  else if p == q2 then (q2, vs, Just q1)
  else                 (p,  vs, f)) cs

sendValue :: Value -> Chan -> [Buffer] -> [Buffer]
sendValue v (p, _) = map (\(q, vs, Nothing) -> if p == q then (q, vs ++ [v], Nothing)
                                               else (q, vs, Nothing))

receiveValue :: Chan -> [Buffer] -> Either (Maybe Value) (Value, [Buffer])
receiveValue (_, p) ((q, [], _):cs)   | p == q = blocked
receiveValue (_, p) ((q, v:vs, f):cs) | p == q = return (v, (q, vs, f):cs)
receiveValue c      (c':cs) =
  do (v, cs') <- receiveValue c cs
     return (v, c':cs')

sendLabel :: Label -> Chan -> [Buffer] -> [Buffer]
sendLabel l (p, _) = map (\(q, vs, Nothing) -> if p == q then (q, vs ++ [VLabel l], Nothing)
                                               else (q, vs, Nothing))

receiveLabel :: Chan -> Env Label (Value -> Thread) -> [Buffer] -> Either (Maybe Value) (Thread, [Buffer])
receiveLabel c@(_, p) bs ((q, [], _):cs) | p == q = blocked
receiveLabel c@(_, p) bs ((q, (VLabel l):vs, f):cs) | p == q =
  do v <- matchLabel c l bs
     return (v, (q, vs, f):cs)
  where
    matchLabel c l bs =
      case lookup l bs of
        Nothing -> blocked  -- really this is a type error so should never occur
        Just f -> return $ f (VChannel c)
receiveLabel c bs (c':cs) =
  do (t, cs') <- receiveLabel c bs cs
     return (t, c':cs')

-- run the current configuration until either
--   * deadlock occurs (guaranteed never to happen by the GV type system)
--   * the top-level exits with a final value 
runConfig :: Configuration -> Configuration
runConfig conf = runConfig' 0 conf where
  -- keep going until all threads are blocked
  runConfig' :: Int -> Configuration -> Configuration
  runConfig' n conf@(cs, ts, next) | n >= length ts = conf
  runConfig' n conf@(cs, t:ts, next) =
    case runCommand t cs ts next of
      Left Nothing  -> runConfig' (n+1) (cs, ts ++ [t], next)
      Left (Just v) -> conf
      Right conf    -> runConfig conf

runProgram :: Term -> Value
runProgram e =
  let (cs, t:ts, next) = runConfig ([], [runPure [] e >>= sexit], 0) in
  case t of
    SExit v -> v
    _       -> error ("Deadlock!")
