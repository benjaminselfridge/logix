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
calculi = [g3c, g3i, g0c, g0i, g0ip_em, g3ipm, g4ip, hilbert]

--------------------------------------------------------------------------------
-- Calculi definitions

p = PredPat "P"
a = FormPat "A"
b = FormPat "B"
c = FormPat "C"
d = FormPat "D"
e = FormPat "E"
gamma  = SetPat "Γ"
gamma' = SetPat "Γ'"
delta  = SetPat "Δ"
delta' = SetPat "Δ'"
a_x_y = SubstPat "x" (VarPat "y") "A"
a_x_t = SubstPat "x" (TermPat "t") "A"
forall_x_a = ForallPat "x" a
exists_x_a = ExistsPat "x" a
nofree_y = NoFreePat "y"

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

g3c :: Calculus
g3c = Calculus {
  name = "g3c",
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
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [delta] ],
            [forall_x_a, gamma] ::=> [delta]))
  , ("Rforall", ([ [gamma] ::=> [delta, a_x_y] ],
            [nofree_y gamma] ::=> [nofree_y delta, nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [delta] ],
            [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y delta]))
  , ("Rexists", ([ [gamma] ::=> [delta, exists_x_a, a_x_t] ],
            [gamma] ::=> [delta, exists_x_a]))
  ]}

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

g3i :: Calculus
g3i = Calculus {
  name = "g3i",
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
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [c] ],
            [ forall_x_a, gamma] ::=> [c]))
  , ("Rforall", ([ [gamma] ::=> [a_x_y] ],
            [nofree_y gamma] ::=> [nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [c] ],
            [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y c]))
  , ("Rexists", ([ [gamma] ::=> [a_x_t] ],
            [gamma] ::=> [exists_x_a]))
  ]}

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

g4ip :: Calculus
g4ip = Calculus {
  name = "g4ip",
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
  , ("L0->", ([ [p, b, gamma] ::=> [e] ],
              [p, p $> b, gamma] ::=> [e]))
  , ("L&->", ([ [c $> (d $> b), gamma] ::=> [e] ],
              [(c $& d) $> b, gamma] ::=> [e]))
  , ("L|->", ([ [c $> b, d $> b, gamma] ::=> [e] ],
              [(c $| d) $> b, gamma] ::=> [e]))
  , ("L->>", ([ [c, d $> b, gamma] ::=> [d], [b, gamma] ::=> [e] ],
              [(c $> d) $> b, gamma] ::=> [e]))
  , ("L_|_", ([],
              [botpat, gamma] ::=> [c]))
  ]}

g0i :: Calculus
g0i = Calculus {
  name = "g0i",
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
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [c] ],
            [ forall_x_a, gamma] ::=> [c]))
  , ("Rforall", ([ [gamma] ::=> [a_x_y] ],
            [nofree_y gamma] ::=> [nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [c] ],
            [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y c]))
  , ("Rexists", ([ [gamma] ::=> [a_x_t] ],
            [gamma] ::=> [exists_x_a]))
  , ("Wk", ([ [gamma] ::=> [c] ],
            [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
             [a, gamma] ::=> [c]))
  ]}

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
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [c] ],
            [ forall_x_a, gamma] ::=> [c]))
  , ("Rforall", ([ [gamma] ::=> [a_x_y] ],
            [nofree_y gamma] ::=> [nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [c] ],
            [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y c]))
  , ("Rexists", ([ [gamma] ::=> [a_x_t] ],
            [gamma] ::=> [exists_x_a]))
  , ("Wk", ([ [gamma] ::=> [c] ],
            [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
             [a, gamma] ::=> [c]))
  ]}

g0c :: Calculus
g0c = Calculus {
  name = "g0c",
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
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [delta] ],
            [forall_x_a, gamma] ::=> [delta]))
  , ("Rforall", ([ [gamma] ::=> [delta, a_x_y] ],
            [nofree_y gamma] ::=> [nofree_y delta, nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [delta] ],
            [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y delta]))
  , ("Rexists", ([ [gamma] ::=> [delta, exists_x_a, a_x_t] ],
            [gamma] ::=> [delta, exists_x_a]))
  , ("LW",   ([ [gamma] ::=> [delta] ],
                [a, gamma] ::=> [delta]))
  , ("RW",   ([ [gamma] ::=> [delta] ],
                [gamma] ::=> [delta, a]))
  , ("LC",   ([ [a, a, gamma] ::=> [delta] ],
                [a, gamma] ::=> [delta]))
  , ("RC",   ([ [gamma] ::=> [delta, a, a] ],
                [gamma] ::=> [delta, a]))
  ] }

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
