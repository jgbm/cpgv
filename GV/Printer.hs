{-# LANGUAGE FlexibleInstances, OverloadedStrings #-}
module GV.Printer (Pretty(..), displayS, renderPretty) where

import GV.Syntax
import Text.PrettyPrint.Leijen

import GHC.Exts (IsString(..))

instance IsString Doc
    where fromString = text

prec m p n | m <= n    = parens p
           | otherwise = p

instance Pretty Session
    where pretty (Output t s) = "!" <> pretty t <> dot <> pretty s
          pretty (Input t s) = "?" <> pretty t <> dot <> pretty s
          pretty (Sum bs) = "+{" <> align (fillCat (punctuate (comma <> space) [ text v <> colon <+> pretty t | (v, t) <- bs ])) <> "}"
          pretty (Choice bs) = "&{" <> align (fillCat (punctuate (comma <> space) [ text v <> colon <+> pretty t | (v, t) <- bs ])) <> "}"
          pretty OutTerm = "end!"
          pretty InTerm = "end?"
          pretty (Server s) = "$" <> pretty s
          pretty (Service s) = "#" <> pretty s
          pretty (SVar v) = text v
          pretty (Neg v) = "~" <> text v
          pretty (Dual s) = "~" <> pretty s
          pretty (OutputType x s) = "!!" <> text x <> dot <> pretty s
          pretty (InputType x s) = "??" <> text x <> dot <> pretty s

ptyp :: Type -> Int -> Doc
ptyp (LinFun t u) = prec 1 (ptyp t 2 <+> "-@" <+> ptyp u 1)
ptyp (UnlFun t u) = prec 1 (ptyp t 2 <+> "->" <+> ptyp u 1)
ptyp (Tensor t u) = prec 2 (ptyp t 3 <+> "*" <+> ptyp u 2)
ptyp (Lift s)     = const (pretty s)
ptyp UnitType     = const ("Unit")

instance Pretty Pattern
    where pretty (BindName v) = text v
          pretty BindUnit = "()"
          pretty (BindPair v w) = parens (text v <> comma <+> text w)

instance Pretty Type
    where pretty t = ptyp t 0

pterm :: Term -> Int -> Doc
pterm (Var s) = const (text s)
pterm Unit    = const ("unit")
pterm (Link t u) = prec 1 ("link" <+> pterm t 2 <+> pterm u 2)
pterm (LinLam x a t) = prec 1 ("\\" <> text x <> colon <> pretty a <> dot <+> pterm t 1)
pterm (UnlLam x a t) = prec 1 ("!\\" <> text x <> colon <> pretty a <> dot <+> pterm t 1)
pterm (App t u) = prec 1 (pterm t 1 <+> pterm u 2)
pterm (Pair t u) = prec 2 (pterm t 1 <> comma <+> pterm u 1)
pterm (Let p t u) = prec 1 (group (align ("let" <+> pretty p <+> equals <+> pretty t <+> "in" <+> pretty u)))
pterm (Send t u) = prec 1 ("send" <+> pretty t <+> pretty u)
pterm (Receive t) = prec 1 ("receive" <+> pretty t)
pterm (Select l t) = prec 1 ("select" <+> text l <+> pretty t)
pterm (Case x bs) = prec 1 (group ("case" <+> pretty x <$> braces (align (cat (punctuate (semi <> space ) [text l <> colon <+> text y <> dot <>  pretty p | (l, y, p) <- bs])))))
pterm (EmptyCase x ys t) = prec 1 ("case" <+> pretty x <> parens (cat (punctuate comma (map text ys))) <> "{} :" <+> pretty t)
pterm (With x a t u) = prec 1 (group ("with" <+> text x <> comma <+> pretty a <+> "connect" <$>
                                      indent 2 (pretty t) <$>
                                      "to" <$>
                                      indent 2 (pretty u)))
pterm (End t) = prec 1 ("terminate" <+> pretty t)
pterm (Serve x y t) = prec 1 ("serve" <+> text x <> parens (text y) <+> equals <+> pretty t)
pterm (Request x) = prec 1 ("request" <+> text x)
pterm (SendType s t) = prec 1 ("sendType" <+> pretty s <+> pretty t)
pterm (ReceiveType t) = prec 2 ("receiveType" <+> pretty t)

instance Pretty Term
    where pretty t = pterm t 0

instance Pretty Assertion
    where pretty (Assert b t a) = group (align (fillCat (punctuate (comma <> space) [text v <> colon <+> pretty a | (v,a) <- b])) <+> "|-" <$>
                                         pretty t <$>
                                         colon <+> pretty a)
