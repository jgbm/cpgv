{-# LANGUAGE FlexibleInstances, OverloadedStrings, TypeSynonymInstances #-}
module CP.Printer (Pretty(..), renderPretty, displayS) where

import CP.Syntax
import Text.PrettyPrint.Leijen

import GHC.Exts (IsString(..))

instance IsString Doc
    where fromString = text

prec m p n | m <= n    = parens p
           | otherwise = p

propBinder k x a = hang 2 (group (text k <+> text x <> dot <$> prop a 0))

prop (Univ x a)    = prec 0 (propBinder "forall" x a)
prop (Exist x a)   = prec 0 (propBinder "exists" x a)
prop (FOUniv t a)  = prec 0 (text "forall" <+> pretty t <> dot <$> prop a 0)
prop (FOExist t a) = prec 0 (text "forall" <+> pretty t <> dot <$> prop a 0)
prop (Mu x a)      = prec 0 (propBinder "mu" x a)
prop (Nu x a)      = prec 0 (propBinder "nu" x a)
prop (OfCourse a)  = prec 2 ("!" <> prop a 2)
prop (WhyNot a)    = prec 2 ("?" <> prop a 2)
prop (Times a b)   = prec 1 (group (prop a 2 <+> "*" <$> prop b 2))
prop (Par a b)     = prec 1 (group (prop a 2 <+> "||" <$> prop b 2))
prop One           = const "1"
prop Bottom        = const "bot"
prop (Plus ps)     = prec 1 (group ("+{" <> align (cat (punctuate (comma <> space) [text v <> colon <+> prop a 0 | (v, a) <- ps]) <> "}")))
prop (With ps)     = prec 1 (group ("&{" <> align (cat (punctuate (comma <> space) [text v <> colon <+> prop a 0 | (v, a) <- ps]) <> "}")))
prop (Var s [])    = const (text s)
prop (Var s args)  = const (hang 2 (group (text s <> parens (fillCat (punctuate comma (map (flip prop 0) args))))))
prop (Neg s)       = const ("~" <> text s)
prop (Dual a)      = const ("~" <> (prop a 2))

instance Pretty Prop
    where pretty p = prop p 0

instance Pretty FOType
    where pretty Int                    = "int"
          pretty Bool                   = "bool"
          pretty Unit                   = "()"
          pretty (t@(_ `To` _)  `To` u) = parens (pretty t) <+> text "->" <+> pretty u
          pretty (t `To` u)             = pretty t <+> text "->" <+> pretty u
          pretty (TQuote b)             = brackets (pretty b)

bar = text "|"
slash = text "/"

instance Pretty Arg
    where pretty (ProcArg p) = pretty p
          pretty (NameArg n) = text n

name s = text (takeWhile ('\'' /=) s)

instance Pretty Proc
    where pretty (ProcVar v []) = name v
          pretty (ProcVar v args) = hang 2 (name v <> parens (fillCat (punctuate (comma <> space) (map pretty args))))
          pretty (Link x w) = name x <> "<->" <> name w
          pretty (Cut x a p q) = hang 2 (group ("cut" <+> brackets (name x <> colon <+> pretty a) <$>
                                                parens (align (pretty p <+> bar <$> pretty q))))
          pretty (Out x y p q) = hang 2 (group (name x <> brackets (name y) <> dot <$$>
                                                parens (align (pretty p <+> bar <$> pretty q))))
          pretty (In x y p) = hang 2 (name x <> parens (name y) <> dot <//> pretty p)
          pretty (Select x l p) = hang 2 (name x <> slash <> text l <> dot <//> pretty p)
          pretty (Case x bs) = hang 2 (group ("case" <+> name x <$> braces (align (cat (punctuate (semi <> space ) [text l <> colon <+> pretty p | (l, p) <- bs])))))
          pretty (Unroll x p) = hang 2 ("unr" <+> name x <> dot <//> pretty p)
          pretty (Roll x y a p q) = hang 2 (group ("roll" <+> name x <+> brackets (name y <> colon <+> pretty a) <$>
                                                   parens (pretty p <> comma <$> pretty q)))
          pretty (Replicate x y p) = hang 2 ("!" <> name x <> parens (name y) <> dot <//> pretty p)
          pretty (Derelict x y p) = hang 2 ("?" <> name x <> brackets (name y) <> dot <//> pretty p)
          pretty (SendProp x a p) = hang 2 (name x <> brackets (pretty a) <> dot <//> pretty p)
          pretty (ReceiveProp x a p) = hang 2 (name x <> parens (pretty a) <> dot <//> pretty p)
          pretty (SendTerm x m p) = hang 2 (name x <> text "*" <> brackets (pretty m) <> dot <//> pretty p)
          pretty (ReceiveTerm x i p) = hang 2 (name x <> text "*" <> parens (name i) <> dot <//> pretty p)
          pretty (EmptyOut x) = name x <> "[].0"
          pretty (EmptyIn x p) = hang 2 (name x <> "()." <//> pretty p)
          pretty (EmptyCase x ys) = "case" <+> name x <> parens (cat (punctuate (comma <> space) (map name ys))) <> "{}"
          pretty (Quote m _) = brackets (pretty m)
          pretty (Unk []) = "?"
          pretty (Unk ys) = "?" <> parens (cat (punctuate (comma <> space) (map name ys)))

instance Pretty Param
    where pretty (ProcParam s) = name s
          pretty (NameParam s) = name s

foterm (ELam x t m) = prec 0 (hang 2 (text "\\" <+> name x <> colon <+> pretty t <> dot <//> foterm m 0))
foterm (EIf m n o) = prec 0 (text "if" <+> foterm m 0 </> text "then" <+> foterm n 0 </> text "else" <+> foterm o 0)
foterm (EApp (EApp (EVar "+") e) e') = prec 1 (foterm e 1 <+> text "+" <+> foterm e' 1)
foterm (EApp (EApp (EVar "*") e) e') = prec 2 (foterm e 2 <+> text "*" <+> foterm e' 2)
foterm (EApp e e') = prec 3 (foterm e 3 <+> foterm e' 2)
foterm (EVar s) = const (name s)
foterm (EBool True) = const (text "true")
foterm (EBool False) = const (text "false")
foterm (EInt i) = const (integer i)
foterm EUnit = const (text "()")
foterm (EQuote p b) = const (brackets (pretty p </> text "|-" <+> pretty b))

instance Pretty FOTerm
    where pretty x = foterm x 0


defn x [] z = name x <+> equals <+> pretty z
defn x ps z = name x <> parens (cat (punctuate (comma <> space) (map pretty ps))) <+> equals <+> pretty z

instance Pretty Defn
    where pretty (ProcDef x ps p) = "def" <+> defn x ps p
          pretty (PropDef x ps a) = "type" <+> defn x ps a

instance Pretty Behavior
    where pretty b = align (fillCat (punctuate (comma <> space) [name v <> colon <+> pretty a | (v,a) <- b]))

instance Pretty Assertion
    where pretty (Assert p b check) = hang 2 (group ((if check then "check " else empty) <>
                                                     pretty p <$>
                                                     "|-" <+> pretty b))

instance Pretty (Either Defn Assertion)
    where pretty (Left d) = pretty d
          pretty (Right a) = pretty a
