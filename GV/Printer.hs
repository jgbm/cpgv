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
          pretty (Server s) = "%" <> pretty s
          pretty (Service s) = "#" <> pretty s
          pretty (SVar v) = text v
          pretty (Neg v) = "~" <> text v
          pretty (OutputType x s) = "!" <> brackets (text x) <> dot <> pretty s
          pretty (InputType x s) = "?" <> brackets (text x) <> dot <> pretty s

ptyp :: Type -> Int -> Doc
ptyp (LinFun t u) = prec 1 (ptyp t 2 <+> "-@" <+> ptyp u 1)
ptyp (UnlFun t u) = prec 1 (ptyp t 2 <+> "->" <+> ptyp u 1)
ptyp (Tensor t u) = prec 2 (ptyp t 3 <+> "*" <+> ptyp u 2)
ptyp UnitType     = const "unit"
ptyp (Lift s)     = const (pretty s)

instance Pretty Pattern
    where pretty (BindName v) = text v
          pretty (BindPair v w) = parens (text v <> comma <+> text w)

instance Pretty Type
    where pretty t = ptyp t 0

pterm :: Term -> Int -> Doc
pterm (Var s) = const (text s)
pterm (Link t u) = prec 1 ("link" <+> pterm t 2 <+> pterm u 2)
pterm (LinLam x a t) = prec 1 ("\\" <> text x <> colon <> pretty a <+> "=>" <+> pterm t 1)
pterm (UnlLam x a t) = prec 1 ("!\\" <> text x <> colon <> pretty a <+> "=>" <+> pterm t 1)
pterm (App t u) = prec 1 (pterm t 1 <+> pterm u 2)
pterm (Pair t u) = prec 2 (pterm t 1 <> comma <+> pterm u 1)
pterm (Let p t u) = prec 1 (group (align ("let" <+> pretty p <+> equals <+> pretty t <+> "in" <$> pretty u)))
pterm (Send t u) = prec 1 ("send" <+> pterm t 2 <+> pterm u 2)
pterm (Receive t) = prec 1 ("receive" <+> pretty t)
pterm (Select l t) = prec 1 ("select" <+> text l <+> pretty t)
pterm (Case x bs) = prec 1 (group ("case" <+> pretty x <$> braces (align (cat (punctuate (semi <> space) [text l <+> text y <+> "=>" <+>  pretty p | (l, y, p) <- bs])))))
pterm (EmptyCase x ys t) = prec 1 ("case" <+> pretty x <> parens (cat (punctuate comma (map text ys))) <> "{} :" <+> pretty t)
pterm (Fork x a t) = prec 1 (group (align (hang 2 ("fork" <+> text x <> colon <+> pretty a<+> "=>" <$> pretty t))))
pterm (Serve x a t) = prec 1 (group (align (hang 2 ("serve" <+> text x <> colon <+> pretty a <+> "=>" <$> pretty t))))
pterm (Request x) = prec 1 ("request" <+> pretty x)
pterm (SendType s t) = prec 1 ("sendType" <+> pretty s <+> pretty t)
pterm (ReceiveType t) = prec 2 ("receiveType" <+> pretty t)
pterm Unit = const "unit"

instance Pretty Term
    where pretty t = pterm t 0

instance Pretty Assertion
    where pretty (Assert b t a) = group (align (fillCat (punctuate (comma <> space) [text v <> colon <+> pretty a | (v,a) <- b])) <+> "|-" <$>
                                         pretty t <$>
                                         colon <+> pretty a)
