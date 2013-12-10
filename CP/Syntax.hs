module CP.Syntax where

data Prop = ForAll String Prop
          | Exists String Prop
          | Mu String Prop
          | Nu String Prop
          | OfCourse Prop
          | WhyNot Prop
          | Times Prop Prop
          | Par Prop Prop
          | One
          | Bottom
          | Plus [(String, Prop)]
          | With [(String, Prop)]
          | Var String [Prop]
          | Neg String
          | Dual Prop
    deriving (Eq, Show)

data Param = ProcParam String | NameParam String
    deriving (Eq, Show)

data Arg   = ProcArg Proc | NameArg String
    deriving (Eq, Show)

data Proc = ProcVar String [Arg]
          | Link String String
          | Cut String Prop Proc Proc
          | Out String String Proc Proc
          | In String String Proc
          | Select String String Proc
          | Case String [(String, Proc)]
          | Unroll String Proc
          | Roll String String Prop Proc Proc
          | Replicate String String Proc
          | Derelict String String Proc
          | SendProp String Prop Proc
          | ReceiveProp String String Proc
          | EmptyOut String
          | EmptyIn String Proc
          | EmptyCase String [String]
          | Unk [String]
    deriving (Eq, Show)

data Defn = ProcDef String [Param] Proc
          | PropDef String [String] Prop
    deriving (Eq, Show)

data Assertion = Assert Proc [(String, Prop)] Bool
    deriving (Eq, Show)
