module Data.Splittable where

import Data.MonoTraversable(Element)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet
import qualified Data.MultiSet.Extras as MSet
import Data.Set (Set)
import qualified Data.Set as Set

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

instance Ord a => Splittable (MultiSet a) where
  split s = [ (s', s'') | s' <- MSet.powerSet s, let s'' = s MSet.\\ s']

  decapitate s = [ (a, s') | a <- MSet.distinctElems s
                             , let s' = MSet.delete a s ]
