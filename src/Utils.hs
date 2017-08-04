{-|
Module      : Utils
Description : Package for defining sequent calculi, and for proof checking and
              generation. 
Copyright   : (c) Ben Selfridge, 2017
License     : GPL-3
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
