{-# LANGUAGE GADTs #-}

-- | Types for classical calculi.
module Logix.Calculi
    ( -- * Types for classical calculi
      ClassicalOp(..)
    , ClassicalQuant(..)
    , ClassicalTerm
    , ClassicalFormula
    , ClassicalSequent
    , (|-)
    , ClassicalAxiom
    , ClassicalRule
    , ClassicalCalculus
      -- * Calculi
    , g3c
      -- * Pretty printing
    , ppClassicalTerm
    , ppClassicalFormula
    , ppClassicalSequent
    ) where

import Logix.Types

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet
import Data.MultiSet.Extras ((<|))
import Data.Splittable
import Data.Text (Text)
import Prettyprinter

-- | Quantifiers for classical logic.
data ClassicalQuant = Forall | Exists
    deriving (Eq, Ord, Show)

-- | And, or, implies, and bottom.
data ClassicalOp = And | Or | Implies | Bottom
    deriving (Eq, Ord, Show)

-- | A term in classical logic.
type ClassicalTerm = Term Text Text

-- | A formula in classical logic.
type ClassicalFormula = 
    Formula Text ClassicalOp ClassicalQuant Text Text

-- | A sequent in classical logic.
type ClassicalSequent = Sequent MultiSet ClassicalFormula

-- | Classical sequent smart constructor.
(|-) :: [ClassicalFormula] -> [ClassicalFormula] -> ClassicalSequent
ants |- sucs = MSet.fromList ants :|- MSet.fromList sucs

type ClassicalAxiom = Axiom ClassicalSequent

data ClassicalRuleArg = VarArg Text | TermArg ClassicalTerm

data ClassicalRuleArgType = VarArgType | TermArgType

type ClassicalRule = Rule ClassicalSequent ClassicalRuleArg

type ClassicalCalculus = Calculus ClassicalSequent ClassicalRuleArg ClassicalRuleArgType

-- | The G3c logic from Negri \& von Plato.
g3c :: ClassicalCalculus
g3c = Calculus
  { calcName = "G3c"
  , calcAxioms = [("Axiom", axiom)]
  , calcRules = [ ("L&", [], andL)
                , ("R&", [], andR)
                , ("L|", [], orL)
                , ("R|", [], orR)
                , ("L->", [], impL)
                , ("R->", [], impR)
                , ("L_|_", [], bottomL)
  ]
  }
  where axiom (ants :|- sucs) = or
            [p == p' | (p@(PredFormula _ _) , _) <- picks ants
                     , (p', _) <- picks sucs
                     , p == p']
        andL (ants :|- sucs) _ =
            [ [ a <| b <| ants' :|- sucs ]
            | (OpFormula And [a, b], ants') <- picks ants ]
        andR (ants :|- sucs) _ =
            [ [ ants :|- a <| sucs', ants :|- b <| sucs' ]
            | (OpFormula And [a, b], sucs') <- picks sucs ]
        orL (ants :|- sucs) _ =
            [ [ a <| ants' :|- sucs, b <| ants' :|- sucs ]
            | (OpFormula Or [a, b], ants') <- picks ants ]
        orR (ants :|- sucs) _ =
            [ [ ants :|- a <| b <| sucs' ]
            | (OpFormula Or [a, b], sucs') <- picks sucs ]
        impL (ants :|- sucs) _ =
            [ [ ants' :|- a <| sucs, b <| ants' :|- sucs ]
            | (OpFormula Implies [a, b], ants') <- picks ants ]
        impR (ants :|- sucs) _ =
            [ [ a <| ants :|- b <| sucs' ]
            | (OpFormula Implies [a, b], sucs') <- picks sucs ]
        bottomL (ants :|- _) _ =
            [ [] | (OpFormula Bottom [], _) <- picks ants ]

ppClassicalTerm :: ClassicalTerm -> Doc ann
ppClassicalTerm (VarTerm x) = pretty x
ppClassicalTerm (FunTerm f ts) = 
    pretty f <> "(" <> hcat (punctuate comma (map ppClassicalTerm ts)) <> ")"

ppClassicalFormula :: ClassicalFormula -> Doc ann
ppClassicalFormula (PredFormula p []) = pretty p
ppClassicalFormula (PredFormula p terms) = 
    pretty p <> "(" <> hcat (punctuate comma (map ppClassicalTerm terms)) <> ")"
ppClassicalFormula (OpFormula Implies [f, g]) =
    "(" <> ppClassicalFormula f <+> "->" <+> ppClassicalFormula g <> ")"
ppClassicalFormula (OpFormula And [f,g]) =
    "(" <> ppClassicalFormula f <+> "&" <+> ppClassicalFormula g <> ")"
ppClassicalFormula (OpFormula Or [f,g]) = 
    "(" <> ppClassicalFormula f <+> "|" <+> ppClassicalFormula g <> ")"
ppClassicalFormula (QuantFormula quant x f) = undefined
ppClassicalFormula f = error $ "bad formula: " ++ show f

ppClassicalSequent :: ClassicalSequent -> Doc ann
ppClassicalSequent = ppSequent ppClassicalFormula
