{-|
Module      : Sequent
Description : Package for defining sequent calculi, and for proof checking and
              generation. 
Copyright   : (c) Ben Selfridge, 2017
License     : GPL-3
Maintainer  : benselfridge@gmail.com
Stability   : experimental

This module is where we define the actual Calculi for logix. It can be edited to
customize the software.

-}

module Calculi
  ( calculi
  ) where

import Calculus

import Data.Char

-- To add your own calculus to logix, define it under the "Calculi definitions"
-- section, and add it to the following list:

-- | All the calculi for logix. To change the default calculus upon startup, simply
-- switch it to the front of the list.
calculi :: [Calculus]
calculi = [g3ip, g3cp, g0ip, g0cp, g0ip_em, g3ipm, hilbert]

--------------------------------------------------------------------------------
-- Calculi definitions

p = AtomPat "P"
a = VarPat "A"
b = VarPat "B"
c = VarPat "C"
gamma  = SetPat "Γ"
gamma' = SetPat "Γ'"
delta  = SetPat "Δ"
delta' = SetPat "Δ'"

-- | Infix AndPat.
($&) = AndPat

-- | Infix OrPat.
($|) = OrPat

-- | Infix ImpliesPat.
($>) = ImpliesPat

-- | Infix iff.
($<>) = \a b -> ImpliesPat a b

-- | Negated pattern.
negpat pat = pat $> botpat

-- | Bottom pattern.
botpat = BottomPat

-- | G3ip, a contraction-free calculus for intuitionistic logic with shared
-- contexts. A good calculus for proof search of intuitionistic formulas.
g3ip :: Calculus
g3ip = Calculus {
  name = "g3ip",
  axioms = [("Axiom", [p, gamma] ::=> [p])],
  rules = 
  [ ("R&", ([ [gamma] ::=> [a], [gamma] ::=> [b] ],
            [gamma] ::=> [a $& b]))
  , ("R|1", ([ [gamma] ::=> [a] ],
             [gamma] ::=> [a $| b]))
  , ("R|2", ([ [gamma] ::=> [b] ],
             [gamma] ::=> [a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [c] ],
            [a $& b, gamma] ::=> [c]))
  , ("L|", ([ [a, gamma] ::=> [c], [b, gamma] ::=> [c] ],
            [a $| b, gamma] ::=> [c]))
  , ("L->", ([ [a $> b, gamma] ::=> [a], [b, gamma] ::=> [c] ],
             [a $> b, gamma] ::=> [c]))
  , ("L_|_", ([],
              [botpat, gamma] ::=> [c]))
  ]}

-- | G3cp, a contraction-free calculus for classical logic with shared contexts. This
-- calculus is ideally suited for proof search, as any given sequent usually has at
-- most one rule that applies to it.
g3cp :: Calculus
g3cp = Calculus {
  name = "g3cp",
  axioms = [("Axiom", [p, gamma] ::=> [delta, p])],
  rules =
  [ ("L&", ([ [a, b, gamma] ::=> [delta] ],
            [a $& b, gamma] ::=> [delta]))
  , ("L|", ([ [a, gamma] ::=> [delta], [b, gamma] ::=> [delta] ],
            [a $| b, gamma] ::=> [delta]))
  , ("L->", ([ [gamma] ::=> [delta, a], [b, gamma] ::=> [delta] ],
             [a $> b, gamma] ::=> [delta]))
  , ("L_|_", ([],
              [botpat, gamma] ::=> [delta]))
  , ("R&", ([ [gamma] ::=> [delta, a], [gamma] ::=> [delta, b] ],
            [gamma] ::=> [delta, a $& b]))
  , ("R|", ([ [gamma] ::=> [delta, a, b] ],
            [gamma] ::=> [delta, a $| b]))
  , ("R->", ([ [a, gamma] ::=> [delta, b] ],
             [gamma] ::=> [delta, a $> b]))
  ]}

-- | G0ip, a calculus for intuitionistic logic with independent contexts. Not a great
-- calculus for proof search due to the independent contexts, and the fact that we
-- usually need to explicitly use weakening and/or contraction in order to prove
-- simple formulas.
g0ip :: Calculus
g0ip = Calculus {
  name = "g0ip",
  axioms = [("Axiom", [a] ::=> [a])],
  rules =
  [ ("R&", ([ [gamma] ::=> [a], [delta] ::=> [b] ],
            [gamma, delta] ::=> [a $& b]))
  , ("R|1", ([ [gamma] ::=> [a] ],
             [gamma] ::=> [a $| b]))
  , ("R|2", ([ [gamma] ::=> [b] ],
             [gamma] ::=> [a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [c] ],
            [a $& b, gamma] ::=> [c]))
  , ("L|", ([ [a, gamma] ::=> [c], [b, delta] ::=> [c] ],
            [a $| b, gamma, delta] ::=> [c]))
  , ("L->", ([ [gamma] ::=> [a], [b, delta] ::=> [c] ],
             [a $> b, gamma, delta] ::=> [c]))
  , ("L_|_", ([],
              [botpat] ::=> [c]))
  , ("Wk", ([ [gamma] ::=> [c] ],
            [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
             [a, gamma] ::=> [c]))
  ]}

-- | G0cp, a calculus for classical logic with independent contexts. Not a great
-- calculus for proof search for the same reasons as G0ip.
g0cp :: Calculus
g0cp = Calculus {
  name = "g0cp",
  axioms = [("Axiom", [a] ::=> [a])],
  rules =
  [ ("R&",   ([ [gamma] ::=> [delta, a], [gamma'] ::=> [delta', b] ],
                [gamma, gamma'] ::=> [delta, delta', a $& b]))
  , ("R|",   ([ [gamma] ::=> [delta, a, b] ],
                [gamma] ::=> [delta, a $| b]))
  , ("R->",  ([ [a, gamma] ::=> [delta, b] ],
                [gamma] ::=> [delta, a $> b]))
  , ("L_|_", ([ ],
              [botpat] ::=> [c]))
  , ("L&",   ([ [a, b, gamma] ::=> [delta] ],
                [a $& b, gamma] ::=> [delta]))
  , ("L|",   ([ [a, gamma] ::=> [delta], [b, gamma'] ::=> [delta'] ],
                [a $| b, gamma, gamma'] ::=> [delta, delta']))
  , ("L->",  ([ [gamma] ::=> [delta, a], [b, gamma'] ::=> [delta'] ],
                [a $> b, gamma, gamma'] ::=> [delta, delta']))
  , ("LW",   ([ [gamma] ::=> [delta] ],
                [a, gamma] ::=> [delta]))
  , ("RW",   ([ [gamma] ::=> [delta] ],
                [gamma] ::=> [delta, a]))
  , ("LC",   ([ [a, a, gamma] ::=> [delta] ],
                [a, gamma] ::=> [delta]))
  , ("RC",   ([ [gamma] ::=> [delta, a, a] ],
                [gamma] ::=> [delta, a]))
  ] }

-- | G0ip with the law of excluded middle, so a classical sequent calculus with
-- independent contexts.
g0ip_em :: Calculus
g0ip_em = Calculus {
  name = "g0ip_em",
  axioms = [("Axiom", [a] ::=> [a])],
  rules =
  [ ("R&", ([ [gamma] ::=> [a], [delta] ::=> [b] ],
            [gamma, delta] ::=> [a $& b]))
  , ("R|1", ([ [gamma] ::=> [a] ],
             [gamma] ::=> [a $| b]))
  , ("R|2", ([ [gamma] ::=> [b] ],
             [gamma] ::=> [a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [c] ],
            [a $& b, gamma] ::=> [c]))
  , ("L|", ([ [a, gamma] ::=> [c], [b, delta] ::=> [c] ],
            [a $| b, gamma, delta] ::=> [c]))
  , ("L->", ([ [gamma] ::=> [a], [b, delta] ::=> [c] ],
             [a $> b, gamma, delta] ::=> [c]))
  , ("L_|_", ([],
              [botpat] ::=> [c]))
  , ("EM", ([ [p, gamma] ::=> [c], [negpat p, delta] ::=> [c] ],
            [gamma, delta] ::=> [c]))
  , ("Wk", ([ [gamma] ::=> [c] ],
            [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
             [a, gamma] ::=> [c]))
  ]}

g3ipm :: Calculus
g3ipm = Calculus {
  name = "g3ipm",
  axioms = [("Axiom", [p, gamma] ::=> [delta, p])],
  rules =
  [ ("L&", ([ [a, b, gamma] ::=> [delta] ],
            [a $& b, gamma] ::=> [delta]))
  , ("L|", ([ [a, gamma] ::=> [delta], [b, gamma] ::=> [delta] ],
            [a $| b, gamma] ::=> [delta]))
  , ("L->", ([ [a $> b, gamma] ::=> [a], [b, gamma] ::=> [delta] ],
             [a $> b, gamma] ::=> [delta]))
  , ("L_|_", ([],
              [botpat, gamma] ::=> [delta]))
  , ("R&", ([ [gamma] ::=> [delta, a], [gamma] ::=> [delta, b] ],
            [gamma] ::=> [delta, a $& b]))
  , ("R|", ([ [gamma] ::=> [delta, a, b] ],
            [gamma] ::=> [delta, a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [delta, a $> b]))
  ]}

-- Adapted from Kleene, Mathematical Logic.
hilbert :: Calculus
hilbert = Calculus {
  name = "hilbert",
  axioms =
  [ ("H1",   [] ::=> [a $> (b $> a)])
  , ("H2",   [] ::=> [(a $> b) $> ((a $> (b $> c)) $> (a $> c))])
  , ("H3",   [] ::=> [a $> (b $> (a $& b))])
  , ("H4a",  [] ::=> [(a $& b) $> a])
  , ("H4b",  [] ::=> [(a $& b) $> b])
  , ("H5a",  [] ::=> [a $> (a $| b)])
  , ("H5b",  [] ::=> [b $> (a $| b)])
  , ("H6",   [] ::=> [(a $> c) $> ((b $> c) $> ((a $| b) $> c))])
  , ("H7",   [] ::=> [(a $> b) $> ((a $> negpat b) $> negpat a)])
  , ("H8",   [] ::=> [negpat (negpat a) $> a])
  , ("H9",   [] ::=> [(a $> b) $> ((b $> a) $> (a $<> b))])
  , ("H10a", [] ::=> [(a $<> b) $> (a $> b)])
  , ("H10b", [] ::=> [(a $<> b) $> (b $> a)])
  ],
  rules = [("MP", ([ [] ::=> [a], [] ::=> [a $> b] ],
                   [] ::=> [b]))]
}
