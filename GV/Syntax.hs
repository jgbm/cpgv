module GV.Syntax where

data Session = Output Type Session
             | Input Type Session
             | Sum [(String, Session)]
             | Choice [(String, Session)]
             | OutTerm
             | InTerm
             | Server Session
             | Service Session
             | SVar String
             | Dual Session
             | Neg String
             | OutputType String Session
             | InputType String Session
    deriving (Eq, Ord, Show)


data Type = LinFun Type Type
          | UnlFun Type Type
          | Tensor Type Type
          | Lift Session
          | UnitType
    deriving (Eq, Ord, Show)

data Pattern = BindName String
             | BindUnit
             | BindPair String String
    deriving (Eq, Ord, Show)

data Term = Var String
          | Unit
          | Link Term Term
          | LinLam String Type Term
          | UnlLam String Type Term
          | App Term Term
          | Pair Term Term
          | Let Pattern Term Term
          | Send Term Term
          | Receive Term
          | Select String Term
          | Case Term [(String, String, Term)]
          | EmptyCase Term [String] Type
          | With String Session Term Term
          | End Term
          | Serve String String Term
          | Request String
          | SendType Session Term
          | ReceiveType Term
    deriving (Eq, Ord, Show)

data Assertion = Assert [(String, Type)] Term Type
