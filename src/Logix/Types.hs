-- | Core logix types: terms, formulas, and sequents.
module Logix.Types 
    ( -- * Terms, formulas, and sequents
      Term(..)
    , Formula(..)
    , Sequent(..)
      -- * Axioms, rules, derivations
    , Axiom
    , Rule
    , Calculus(..)
    -- * Pretty printing
    , ppSequent
    ) where

import qualified Data.MultiSet as MSet
import Data.MultiSet (MultiSet)
import Data.Text (Text)
import Prettyprinter
import Data.Foldable (toList)

-- | A term in first-order predicate calculus. Instantiate @f@ with a type for function symbols and @x@ with a type for variable symbols. @Text@ is a good choice for both types.
data Term f x = VarTerm x
              | FunTerm f [Term f x]
  deriving (Eq, Ord, Show)

-- | A formula in first-order predicate calculus. @p@ is a type for predicate symbols. @Text@ is a good choice for this. @op@ is a type for logical connectives (implies, and, or, not), including connectives that have no arguments (like bottom). @quant@ is a type for quantifiers that bind a single variable symbol. @f@ and @x@ are the function and variable symbols.
data Formula p op quant f x 
    = PredFormula p [Term f x]
    | OpFormula op [Formula p op quant f x]
    | QuantFormula quant x (Formula p op quant f x)
    deriving (Eq, Ord, Show)

-- | A sequent in Gentzen-style sequent calculus. @formula@ is the type of formulas. @c@ is the type for the meta-logical container type. In Gentzen's original formulation of sequent calculus, these were ordered lists, and so Gentzen included special rules for rearranging the elements in the list. In Negri and von Plato's book Structural Proof Theory, they use unordered multisets ("bags").
data Sequent c formula = c formula :|- c formula
  deriving Show
infix 0 :|-

-- | An 'Axiom' is a function which returns @True@ if the given sequent is an instance of a logical axiom.
type Axiom sequent = sequent -> Bool

-- | A 'Rule' is a function which, given a sequent, provides a list of subgoals that, if proven, imply the given sequent. Given a logical derivation rule of the form
--
-- @
--    premises
--   ----------
--   conclusion
-- @
--
-- A 'Rule' is a function which takes a conclusion to all applications of this rule to a particular conclusion to yield a list of premises. Each list of premises in the returned list can replace the original goal in a derivation.
--
-- The extra @arg@ argument is for when the rule needs information supplied that isn't already in the input sequent; for example, what term to instantiate a variable to, or a formula to use in the cut rule.
type Rule sequent arg = sequent -> [arg] -> [[sequent]]

-- | A calculus is a collection of axioms and derivation rules.
data Calculus sequent arg argType = Calculus
    { calcName   :: Text
    , calcAxioms :: [(Text, Axiom sequent)]
    , calcRules  :: [(Text, [argType], Rule sequent arg)]
    }

-- | Pretty-print a @sequent@, given a pretter printer for the @formula@ type.
ppSequent :: Foldable c => (formula -> Doc ann) -> Sequent c formula -> Doc ann
ppSequent ppf (ants :|- sucs) = 
    hcat (punctuate comma (map ppf (toList ants))) <+> "|-" <+> hcat (punctuate comma (map ppf (toList sucs)))
