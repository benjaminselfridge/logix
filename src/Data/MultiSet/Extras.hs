{-# LANGUAGE TypeFamilies #-}
module Data.MultiSet.Extras where

import Data.MultiSet
    ( MultiSet, fromOccurList, singleton, toOccurList, Occur, insert )
import Data.MonoTraversable (Element, MonoPointed(..), MonoFoldable(..))

type instance Element (MultiSet a) = a

instance MonoPointed (MultiSet a) where
  opoint = singleton

instance MonoFoldable (MultiSet a)

-- | The list of all subsets of a multiset.
powerSet :: Ord a => MultiSet a -> [MultiSet a]
powerSet s =
  let occList = toOccurList s
      elts = fst <$> occList
  in [ fromOccurList fixedOccList' | occs <- subOccurs (snd <$> occList)
                                   , let occList' = zip elts occs
                                   , let fixedOccList' = filter ((> 0). snd) occList' ]

subOccurs :: [Occur] -> [[Occur]]
subOccurs [] = [[]]
subOccurs (n:ns) = [ i : is | i <- [0..n], is <- subOccurs ns ]

(<|) :: Ord a => a -> MultiSet a -> MultiSet a
a <| s = insert a s
infixr 5 <|