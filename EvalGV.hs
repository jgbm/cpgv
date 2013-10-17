import Syntax.AbsGV
import Syntax.PrintGV

import Control.Monad
import Data.Maybe

data Value =
   VVar LIdent
 | VUnit
 | VFun LIdent Term
 | VPair Value Value
 | VChannel CIdent
   deriving (Eq,Ord,Show)

valueToTerm :: Value -> Term
valueToTerm (VVar x)     = Var x
valueToTerm VUnit        = Unit
valueToTerm (VFun x e)   = Fun x e
valueToTerm (VPair v w)  = Pair (valueToTerm v) (valueToTerm w)
valueToTerm (VChannel c) = undefined

-- shouldn't need this
-- data EvalContext =
--    Hole
--  | AppFun EvalContext Term
--  | AppArg Value EvalContext
--  | PairLeft EvalContext Term
--  | PairRight Value EvalContext
--  | LetElim Pattern EvalContext Term
--  | SelectElim LIdent EvalContext
--  | CaseElim EvalContext [Branch]
--    deriving (Eq,Ord,Show)


-- runtime channel identifier
type CIdent = Int

type Channel = (CIdent, [Value])
type Gen = Int
type Env k v = [(k, v)]
type VEnv = Env LIdent Value

type Configuration = (VEnv, [Channel], [Term], Gen)

{-
  TODO:
    * refactor split
    * name generation for with
    * code for handling interactions between threads
    * ...
-}

-- a possibly suspended value
data Susp a =
   Result a
 | Split VEnv Term Term
 | SSend Value CIdent (Value -> Susp a)
 | SReceive CIdent (Value -> Susp a)
 | SSelect LIdent CIdent (Value -> Susp a)
 | SCase CIdent [(LIdent, Value)] (Value -> Susp a)

instance Monad Susp where
  return          = Result
  
  --Wait e k' >>= k = Wait e (\v -> k' v >>= k)

split = Split
ssend v c = SSend v c return
sreceive c = SReceive c return
sselect l c = SSelect l c return
scase v bs = SCase v bs return

-- suspend :: Term -> Susp Value
-- suspend e = Wait e return

extend = flip (:)

-- evaluate as much as possible in a single thread
evalThread :: VEnv -> Term -> Susp Value
evalThread env e = evalThread' env e where
  et = evalThread' env
  evalThread' env (Var x)   = return (fromJust (lookup x env))
  evalThread' env Unit      = return VUnit
  evalThread' env (Fun x e) = return (VFun x e)
  evalThread' env (App f a) =
    do VFun x e <- et f
       v <- et a
       evalThread' (extend env (x, v)) e
  evalThread' env (Pair e1 e2) =
    do v1 <- et e1
       v2 <- et e2
       return (VPair v1 v2)
  evalThread' env (Let (BindName x) e1 e2) =
    do v <- et e1
       evalThread' (extend env (x, v)) e2
  evalThread' env (With x e1 e2) =
    split (extend env (x, undefined)) e1 e2
  evalThread' env (End e)        = et e
  evalThread' env (Send m n)     =
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
       let bs' = map (\(Branch l x e) -> (l, VFun x e)) bs
       scase c bs'




eval :: Configuration -> Value
eval = undefined

evalProgram :: Term -> Value
evalProgram e = eval ([], [], [e], 0)
