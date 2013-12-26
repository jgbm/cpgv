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
             | Neg String
             | OutputType String Session
             | InputType String Session
    deriving (Eq, Ord, Show)

dual :: Session -> Session
dual (Output t s) = Input t (dual s)
dual (Input t s)  = Output t (dual s)
dual (Sum cs)     = Choice [(l, dual s) | (l, s) <- cs]
dual (Choice cs)  = Sum [(l, dual s) | (l, s) <- cs]
dual InTerm       = OutTerm
dual OutTerm      = InTerm
dual (Server s)   = Service (dual s)
dual (Service s)  = Server (dual s)
dual (SVar x)     = Neg x
dual (Neg x)      = SVar x
dual (OutputType x s) = InputType x (dual s)
dual (InputType x s)  = OutputType x (dual s)

data Type = LinFun Type Type
          | UnlFun Type Type
          | Tensor Type Type
          | UnitType
          | Lift Session
    deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- Types, substitutions, and unifications

linear :: Type -> Bool
linear (LinFun _ _)       = True
linear (Tensor _ _)       = True
linear (Lift (Service _)) = False
linear (Lift InTerm)      = False
linear (Lift _)           = True
linear _                  = False

unlimited :: Type -> Bool
unlimited = not . linear

--------------------------------------------------------------------------------
-- Free session variables
fsv :: Session -> [String]
fsv (Output t s) = ftv t ++ fsv s
fsv (Input t s) = ftv t ++ fsv s
fsv (Sum ls) = concatMap (fsv . snd) ls
fsv (Choice ls) = concatMap (fsv . snd) ls
fsv OutTerm = []
fsv InTerm = []
fsv (Server s) = fsv s
fsv (Service s) = fsv s
fsv (SVar x) = [x]
fsv (Neg x) = [x]
fsv (OutputType x s) = filter (x /=) (fsv s)
fsv (InputType x s) = filter (x /=) (fsv s)

ftv :: Type -> [String]
ftv (LinFun t u) = ftv t ++ ftv u
ftv (UnlFun t u) = ftv t ++ ftv u
ftv (Tensor t u) = ftv t ++ ftv u
ftv (Lift s) = fsv s

--------------------------------------------------------------------------------
-- Instantiating session variables
instSession :: String -> Session -> Session -> Session
instSession x s (Output t s') = Output (instType x s t) (instSession x s s')
instSession x s (Input t s') = Input (instType x s t) (instSession x s s')
instSession x s (Sum lts) = Sum [(l, instSession x s s') | (l, s') <- lts]
instSession x s (Choice lts) = Choice [(l, instSession x s s') | (l, s') <- lts]
instSession x s OutTerm = OutTerm
instSession x s InTerm = InTerm
instSession x s (Server s') = Server (instSession x s s')
instSession x s (Service s') = Service (instSession x s s')
instSession x s (SVar y) | x == y = s
                         | otherwise = SVar y
instSession x s (Neg y) | x == y = dual s
                        | otherwise = Neg y
instSession x s (OutputType y s') | x == y = OutputType y s'
                                  | otherwise = OutputType y (instSession x s s')
instSession x s (InputType y s') | x == y = InputType y s'
                                  | otherwise = InputType y (instSession x s s')

instType :: String -> Session -> Type -> Type
instType x s (LinFun t u) = LinFun (instType x s t) (instType x s u)
instType x s (UnlFun t u) = LinFun (instType x s t) (instType x s u)
instType x s (Tensor t u) = LinFun (instType x s t) (instType x s u)
instType x s UnitType         = UnitType
instType x s (Lift s') = Lift (instSession x s s')

data Pattern = BindName String
             | BindPair String String
    deriving (Eq, Ord, Show)

data Term = Var String
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
          | Fork String Session Term
          | Serve String Session Term
          | Request Term
          | SendType Session Term
          | ReceiveType Term
          | Unit
    deriving (Eq, Ord, Show)

fv :: Term -> [String]
fv (Var s)                  = [s]
fv (Link m n)               = fv m ++ fv n
fv (LinLam x _ m)           = filter (x /=) (fv m)
fv (UnlLam x _ m)           = filter (x /=) (fv m)
fv (App m n)                = fv m ++ fv n
fv (Pair m n)               = fv m ++ fv n
fv (Let (BindName x) m n)   = fv m ++ filter (x /=) (fv n)
fv (Let (BindPair x y) m n) = fv m ++ filter (\z -> z /= x && z /= y) (fv n)
fv (Send m n)               = fv m ++ fv n
fv (Receive m)              = fv m
fv (Select _ m)             = fv m
fv (Case m bs)              = fv m ++ concat [fv n | (_, _, n) <- bs]
fv (EmptyCase m _ _)        = fv m
fv (Fork x _ m)             = filter (x /=) (fv m)
fv (Serve x _ m)            =  filter (x /=) (fv m)
fv (Request m)              = fv m
fv (SendType _ m)           = fv m
fv (ReceiveType m)          = fv m
fv Unit                     = []

data Assertion = Assert [(String, Type)] Term Type
