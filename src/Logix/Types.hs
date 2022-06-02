-- | Core logix types: terms, formulas, and sequents.
module Logix.Types where

import qualified Data.MultiSet as MSet
import Data.MultiSet (MultiSet)
import Data.Text (Text)

data Term f x = VarTerm x
              | FunTerm f [Term f x]
  deriving (Eq, Ord, Show)

type SimpleTerm = Term Text Text

data Formula p quant op term = PredFormula p [term]
                             | OpFormula op [Formula p quant op term]
                             | QuantFormula quant (Formula p quant op term)
    deriving (Eq, Ord, Show)

data Quantifier = Forall | Exists
    deriving (Eq, Ord, Show)

data Op = And | Or | Implies | Bottom
    deriving (Eq, Ord, Show)

type SimpleFormula = Formula Text Quantifier Op SimpleTerm

data Sequent c formula = c formula :|- c formula
  deriving Show
infix 0 :|-

(|-) :: [SimpleFormula] -> [SimpleFormula] -> SimpleSequent
ants |- sucs = MSet.fromList ants :|- MSet.fromList sucs

type SimpleSequent = Sequent MultiSet SimpleFormula

type Axiom sequent = sequent -> Bool
type Rule sequent = sequent -> [[sequent]]

type SimpleAxiom = Axiom SimpleSequent
type SimpleRule = Rule SimpleSequent

data Calculus sequent = Calculus
    { calcName   :: Text
    , calcAxioms :: [(Text, Axiom sequent)]
    , calcRules  :: [(Text, Rule sequent)]
    }

type SimpleCalculus = Calculus SimpleSequent
