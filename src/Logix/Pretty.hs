{-# LANGUAGE OverloadedStrings #-}

module Logix.Pretty where

import Logix.Types
    ( Formula(QuantFormula, PredFormula, OpFormula),
      SimpleTerm,
      Term(FunTerm, VarTerm),
      SimpleSequent,
      Sequent(..),
      SimpleFormula,
      Op(Or, Implies, And) )

import Data.Foldable (Foldable(toList))
import Data.Text (Text, intercalate)
import Prettyprinter
    ( Doc, comma, (<+>), hcat, punctuate, Pretty(pretty) )

ppSequent :: Foldable c => (formula -> Doc ann) -> Sequent c formula -> Doc ann
ppSequent ppf (ants :|- sucs) = 
    hcat (punctuate comma (map ppf (toList ants))) <+> "|-" <+> hcat (punctuate comma (map ppf (toList sucs)))

ppSimpleSequent :: SimpleSequent -> Doc ann
ppSimpleSequent = ppSequent ppSimpleFormula

ppSimpleFormula :: SimpleFormula -> Doc ann
ppSimpleFormula (PredFormula p []) = pretty p
ppSimpleFormula (PredFormula p terms) = 
    pretty p <> "(" <> hcat (punctuate comma (map ppSimpleTerm terms)) <> ")"
ppSimpleFormula (OpFormula Implies [f, g]) =
    "(" <> ppSimpleFormula f <+> "->" <+> ppSimpleFormula g <> ")"
ppSimpleFormula (OpFormula And [f,g]) =
    "(" <> ppSimpleFormula f <+> "&" <+> ppSimpleFormula g <> ")"
ppSimpleFormula (OpFormula Or [f,g]) = 
    "(" <> ppSimpleFormula f <+> "|" <+> ppSimpleFormula g <> ")"
ppSimpleFormula (QuantFormula quant f) = undefined
ppSimpleFormula f = error $ "bad formula: " ++ show f

ppSimpleTerm :: SimpleTerm -> Doc ann
ppSimpleTerm (VarTerm x) = pretty x
ppSimpleTerm (FunTerm f ts) = 
    pretty f <> "(" <> hcat (punctuate comma (map ppSimpleTerm ts)) <> ")"