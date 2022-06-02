{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Scratch where

import Calculus ( Formula(..), UniName (..), Derivation (prems) )
import Data.Text (Text)

import Data.MonoTraversable (Element, MonoPointed (opoint), MonoFoldable, onull)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet
-- import qualified Data.MultiSet.Extras as MSet
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text, pack)
import Data.Functor.Identity (Identity)
import Control.Applicative (Alternative, liftA2)
import Data.Containers (IsSet (filterSet), SetContainer (ContainerKey))
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import System.Posix.Internals (c_ftruncate, c_access)
import PPCalculus (ppFormulaList)
-- import Control.Lens ()

type instance Element (MultiSet a) = a

instance MonoPointed (MultiSet a) where
  opoint = MSet.singleton

instance MonoFoldable (MultiSet a)

-- | A container for which we can enumerate all ways to split the container in two such that we can recombine them with @<>@.
--
-- Laws:
-- 
-- @
--   1. elem (c', c'') (split c) == (c' <> c'' == c).
--   2. elem (a, c') (decapitate c) == (opoint a <> c' == c).
--   3. Neither split nor decapitate contain any repeated elements.
-- @
class Splittable c where
  -- | All ways to split the container into two pieces.
  split :: c -> [(c, c)]
  -- | All ways to decapitate the container.
  decapitate :: c -> [(Element c, c)]

instance Splittable [a] where
  split [] = [([],[])]
  split (a:as) = ([], a:as) : [ (a:as', as'') | (as', as'') <- split as ]

  decapitate [] = []
  decapitate (a:as) = [(a, as)]

instance Ord a => Splittable (Set a) where
  split s = [ (s', s'') | s' <- Set.toList (Set.powerSet s)
                        , let s'' = s Set.\\ s' ]

  decapitate s = [ (a, s') | a <- Set.toList s, let s' = Set.delete a s ]


-- | The list of all subsets of a multiset.
powerSet :: Ord a => MultiSet a -> [MultiSet a]
powerSet s =
  let occList = MSet.toOccurList s
      elts = fst <$> occList
  in [ MSet.fromOccurList fixedOccList' | occs <- subOccurs (snd <$> occList)
                                   , let occList' = zip elts occs
                                   , let fixedOccList' = filter ((> 0). snd) occList' ]

subOccurs :: [MSet.Occur] -> [[MSet.Occur]]
subOccurs [] = [[]]
subOccurs (n:ns) = [ i : is | i <- [0..n], is <- subOccurs ns ]

instance Ord a => Splittable (MultiSet a) where
  split s = [ (s', s'') | s' <- powerSet s, let s'' = s MSet.\\ s']

  decapitate s = [ (a, s') | a <- MSet.distinctElems s
                             , let s' = MSet.delete a s ]

data SplitMatcher c = MatchOne (Element c -> Bool)
                    | MatchSome (c -> Bool)

data SplitMatch c = One (Element c)
                  | Some c

deriving instance (Show c, Show (Element c)) => Show (SplitMatch c)
deriving instance (Eq c, Eq (Element c)) => Eq (SplitMatch c)
deriving instance (Ord c, Ord (Element c)) => Ord (SplitMatch c)

type SplitPattern c = [(Text, SplitMatcher c)]

splitMatch :: (MonoFoldable c, Splittable c) => SplitPattern c -> c -> [Map Text (SplitMatch c)]
splitMatch [] c | onull c = [Map.empty]
           | otherwise = []
splitMatch ((binder, pat):pats) c =
  let f m = Map.insert binder m
  in case pat of
       MatchOne p -> [ f (One a) matchRest 
                     | (a, c') <- decapitate c
                     , p a
                     , matchRest <- splitMatch pats c']
       MatchSome p -> [ f (Some c') matchRest
                      | (c', c'') <- split c
                      , p c'
                      , matchRest <- splitMatch pats c'' ]

g3c :: Calculus
g3c = Calculus { rules = []
               , axioms = [("Axiom", g3cAxiom)]
               }


-- ^ An axiom is a function that determines whether a given sequent is an instance of the axiom.
type Axiom = Sequent -> Bool

-- ^ A rule is a function from a conclusion to a list of premises that the conclusion can be replaced by.
type Rule = Sequent -> [[Sequent]]

data Calculus = Calculus { rules :: [(Text, Rule)]
                         , axioms :: [(Text, Axiom)]
                         }

data Sequent = MultiSet Formula :|- MultiSet Formula

instance Show Sequent where
    show (gamma :|- delta) = 
      show (MSet.toList gamma) ++ " |- " ++ show (MSet.toList delta)

(|-) :: [Formula] -> [Formula] -> Sequent
ants |- sucs = MSet.fromList ants :|- MSet.fromList sucs

g3cAxiom :: Axiom
g3cAxiom (prems :|- concs) = or
    [ prem == conc | (prem, _) <- decapitate prems
                   , (conc, _) <- decapitate concs 
                   , prem == conc
                   , Pred _ _ <- [prem]
                   ]

andOp :: UniName
andOp = UniName ("&","&")
orOp :: UniName
orOp = UniName ("|","|")
impOp :: UniName
impOp = UniName ("->", "->")

g3cAndR :: Rule
g3cAndR (prems :|- concs) =
  [ [ prems :|- MSet.insert a concs', prems :|- MSet.insert b concs' ]
  | (BinaryOp op a b, concs') <- decapitate concs
  , op == andOp ]

g3cAndL :: Rule
g3cAndL (prems :|- concs) = 
  [ [ MSet.insert a (MSet.insert b prems') :|- concs]
  | (BinaryOp op a b, prems') <- decapitate prems
  , op == andOp ]

g3cOrR :: Rule
g3cOrR (prems :|- concs) =
  [ [ prems :|- MSet.insert a (MSet.insert b concs') ]
  | (BinaryOp op a b, concs') <- decapitate concs
  , op == orOp ]

g3cOrL :: Rule
g3cOrL (prems :|- concs) =
  [ [ MSet.insert a prems' :|- concs, MSet.insert b prems' :|- concs ]
  | (BinaryOp op a b, prems') <- decapitate prems
  , op == orOp]

g3cImpR :: Rule
g3cImpR (prems :|- concs) =
  [ [ MSet.insert a prems :|- concs' ]
  | (BinaryOp op a b, concs') <- decapitate prems
  , op == impOp ]

p :: Formula
p = Pred "P" []
q :: Formula
q = Pred "Q" []
(.&) :: Formula -> Formula -> Formula
(.&) = BinaryOp andOp
(.|) :: Formula -> Formula -> Formula
(.|) = BinaryOp orOp