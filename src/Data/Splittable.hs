module Data.Splittable (Splittable(..)) where

import Data.MonoTraversable(Element, MonoPointed)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet
import qualified Data.MultiSet.Extras as MSet
import Data.Set (Set)
import qualified Data.Set as Set

-- | A @Splittable@ is a container for which we can enumerate all ways to split the container in two such that we can recombine them with @<>@. This can be useful for pattern matching.
--
-- >>> xs = [True, False, False, True, True, True, False, False]
-- >>> mapM_ print [ (fs, rst) | (True, xs1) <- picks xs, (fs, rst) <- splits xs1, all not fs ]
-- ([],[False,False,True,True,True,False,False])
-- ([False],[False,True,True,True,False,False])
-- ([False,False],[True,True,True,False,False])
class (Monoid c, MonoPointed c) => Splittable c where
  -- | All ways to pick a single element the container.
  picks :: c -> [(Element c, c)]
  -- | All ways to split the container into two pieces.
  splits :: c -> [(c, c)]

instance Splittable [a] where
  splits [] = [([],[])]
  splits (a:as) = ([], a:as) : [ (a:as', as'') 
                               | (as', as'') <- splits as ]

  picks [] = []
  picks (a:as) = [(a, as)]

instance Ord a => Splittable (Set a) where
  splits s = [ (s', s'') | s' <- Set.toList (Set.powerSet s)
                         , let s'' = s Set.\\ s' ]

  picks s = [ (a, s') | a <- Set.toList s, let s' = Set.delete a s ]

instance Ord a => Splittable (MultiSet a) where
  splits s = [ (s', s'') | s' <- MSet.powerSet s, let s'' = s MSet.\\ s']

  picks s = [ (a, s') | a <- MSet.distinctElems s
                      , let s' = MSet.delete a s ]
