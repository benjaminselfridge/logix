{-|
Module      : Utils
Description : Utility functions
Copyright   : (c) Ben Selfridge, 2017
License     : BSD3
Maintainer  : benselfridge@gmail.com
Stability   : experimental

-}

module Utils where

import Data.List

appendPair :: ([a],[b]) -> ([a],[b]) -> ([a],[b])
appendPair (xs, ys) (xs', ys') = (xs ++ xs', ys ++ ys')

concatPairs :: [([a],[b])] -> ([a],[b])
concatPairs = foldl appendPair ([],[])

nubPair :: (Eq a, Eq b) => ([a],[b]) -> ([a],[b])
nubPair (xs, ys) = (nub xs, nub ys)

nubPairBy :: (a -> a -> Bool) -> (b -> b -> Bool) -> ([a],[b]) -> ([a],[b])
nubPairBy f g (xs, ys) = (nubBy f xs, nubBy g ys)

(!!!) :: [a] -> Int -> Maybe a
infixl 9 !!!
(x:xs) !!! n | n == 0    = Just x
             | n <  0    = Nothing
             | otherwise = xs !!! (n-1)
_ !!! _ = Nothing

readMaybe :: Read a => String -> Maybe a
readMaybe s = case reads s of
                [] -> Nothing
                [(a, _)] -> Just a

setElt :: Int -> a -> [a] -> [a]
setElt _ _ [] = []
setElt 0 x (y:ys) = x : ys
setElt n x (y:ys) | n > 0 = y : (setElt (n-1) x ys)

pickPair :: Bool -> (a,a) -> a
pickPair False = fst
pickPair True  = snd

keyElem :: (Eq a) => a -> [(a,b)] -> Bool
keyElem x pairs = case lookup x pairs of
  Nothing -> False
  Just _  -> True

oneOfEach :: [[a]] -> [[a]]
oneOfEach ((x:xs):rst) = [ x : l | l <- oneOfEach rst ] ++ oneOfEach (xs:rst)
oneOfEach ([]:rst) = []
oneOfEach [] = [[]]

extractSingleton :: [a] -> Maybe a
extractSingleton [x] = Just x
extractSingleton _   = Nothing
