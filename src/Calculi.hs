{-|
Module      : Calculi
Description : Definitions of sequent calculi for use in logix.
Copyright   : (c) Ben Selfridge, 2017
License     : BSD3
Maintainer  : benselfridge@gmail.com
Stability   : experimental

This module is where we define the actual Calculi for logix. It can be edited to
customize the software.

-}

module Calculi
  ( calculi
  , andForm
  , orForm
  , impliesForm
  , forallForm
  , existsForm
  ) where

import Calculus

import Data.Char

-- To add your own calculus to logix, define it under the "Calculi definitions"
-- section, and add it to the following list:

-- | All the calculi for logix. To change the default calculus upon startup, simply
-- switch it to the front of the list.
calculi :: [Calculus]
calculi = [g3c, g3i, g0c, g0i, g3ipm, g4ip, wll]

--------------------------------------------------------------------------------
-- Calculi definitions

-- formula connectives
botForm     = ZeroaryOp (UniName ("_|_", "⊥"))
andForm     = BinaryOp (UniName ("&","&"))
orForm      = BinaryOp (UniName ("|","∨"))
impliesForm = BinaryOp (UniName ("->","⊃"))
forallForm  = Quant (UniName ("forall ","∀"))
existsForm  = Quant (UniName ("exists ","∃"))

-- connective patterns
botPat     = ZeroaryOpPat (UniName ("_|_", "⊥"))
andPat     = BinaryOpPat (UniName ("&","&"))
orPat      = BinaryOpPat (UniName ("|","∨"))
impliesPat = BinaryOpPat (UniName ("->","⊃"))
forallPat  = QuantPat (UniName ("forall ","∀"))
existsPat  = QuantPat (UniName ("exists ","∃"))

-- base patterns
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

-- abbreviations
neg = UAbbrev (UniName ("~", "¬")) "A" (impliesPat a botPat)
iff = BAbbrev (UniName ("<->", "↔")) "A" "B" (andPat (impliesPat a b) (impliesPat b a))

-- quantifier and subst patterns
a_x_y = SubstPat "x" (VarPat "y") "A"
a_x_t = SubstPat "x" (TermPat "t") "A"
forall_x_a = forallPat "x" a
exists_x_a = existsPat "x" a
nofree_y = NoFreePat "y"

-- | Infix andPat.
($&) = andPat

-- | Infix orPat.
($|) = orPat

-- | Infix impliesPat.
($>) = impliesPat

g3c :: Calculus
g3c = Calculus {
  calcName = "G3c",
  axioms = [("Axiom", [p, gamma] ::=> [delta, p])],
  rules =
  [ ("R&", ([ [gamma] ::=> [delta, a], [gamma] ::=> [delta, b] ],
            [gamma] ::=> [delta, a $& b]))
  , ("R|", ([ [gamma] ::=> [delta, a, b] ],
            [gamma] ::=> [delta, a $| b]))
  , ("R->", ([ [a, gamma] ::=> [delta, b] ],
             [gamma] ::=> [delta, a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [delta] ],
            [a $& b, gamma] ::=> [delta]))
  , ("L|", ([ [a, gamma] ::=> [delta], [b, gamma] ::=> [delta] ],
            [a $| b, gamma] ::=> [delta]))
  , ("L->", ([ [gamma] ::=> [delta, a], [b, gamma] ::=> [delta] ],
             [a $> b, gamma] ::=> [delta]))
  , ("L_|_", ([],
              [botPat, gamma] ::=> [delta]))
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [delta] ],
            [forall_x_a, gamma] ::=> [delta]))
  , ("Rforall", ([ [gamma] ::=> [delta, a_x_y] ],
            [nofree_y gamma] ::=> [nofree_y delta, nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [delta] ],
            [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y delta]))
  , ("Rexists", ([ [gamma] ::=> [delta, exists_x_a, a_x_t] ],
            [gamma] ::=> [delta, exists_x_a]))
  ],
  uAbbrevs = [neg],
  bAbbrevs = [iff]
  }

g3i :: Calculus
g3i = Calculus {
  calcName = "G3i",
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
              [botPat, gamma] ::=> [c]))
  , ("Lforall", ([ [a_x_t, forall_x_a, gamma] ::=> [c] ],
            [ forall_x_a, gamma] ::=> [c]))
  , ("Rforall", ([ [gamma] ::=> [a_x_y] ],
            [nofree_y gamma] ::=> [nofree_y forall_x_a]))
  , ("Lexists", ([ [a_x_y, gamma] ::=> [c] ],
            [nofree_y exists_x_a, nofree_y gamma] ::=> [nofree_y c]))
  , ("Rexists", ([ [gamma] ::=> [a_x_t] ],
            [gamma] ::=> [exists_x_a]))
  ],
  uAbbrevs = [neg],
  bAbbrevs = [iff]
  }

g0c :: Calculus
g0c = Calculus {
  calcName = "G0c",
  axioms = [("Axiom", [a] ::=> [a])],
  rules =
  [ ("R&",   ([ [gamma] ::=> [delta, a], [gamma'] ::=> [delta', b] ],
                [gamma, gamma'] ::=> [delta, delta', a $& b]))
  , ("R|",   ([ [gamma] ::=> [delta, a, b] ],
                [gamma] ::=> [delta, a $| b]))
  , ("R->",  ([ [a, gamma] ::=> [delta, b] ],
                [gamma] ::=> [delta, a $> b]))
  , ("L_|_", ([ ],
              [botPat] ::=> [c]))
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
  ] ,
  uAbbrevs = [neg],
  bAbbrevs = [iff]
  }

g0i :: Calculus
g0i = Calculus {
  calcName = "G0i",
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
              [botPat] ::=> [c]))
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
  ],
  uAbbrevs = [neg],
  bAbbrevs = [iff]
  }

g3ipm :: Calculus
g3ipm = Calculus {
  calcName = "G3ipm",
  axioms = [("Axiom", [p, gamma] ::=> [delta, p])],
  rules =
  [ ("R&", ([ [gamma] ::=> [delta, a], [gamma] ::=> [delta, b] ],
            [gamma] ::=> [delta, a $& b]))
  , ("R|", ([ [gamma] ::=> [delta, a, b] ],
            [gamma] ::=> [delta, a $| b]))
  , ("R->", ([ [a, gamma] ::=> [b] ],
             [gamma] ::=> [delta, a $> b]))
  , ("L&", ([ [a, b, gamma] ::=> [delta] ],
            [a $& b, gamma] ::=> [delta]))
  , ("L|", ([ [a, gamma] ::=> [delta], [b, gamma] ::=> [delta] ],
            [a $| b, gamma] ::=> [delta]))
  , ("L->", ([ [a $> b, gamma] ::=> [a], [b, gamma] ::=> [delta] ],
             [a $> b, gamma] ::=> [delta]))
  , ("L_|_", ([],
              [botPat, gamma] ::=> [delta]))
  ],
  uAbbrevs = [neg],
  bAbbrevs = [iff]
  }

g4ip :: Calculus
g4ip = Calculus {
  calcName = "G4ip",
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
              [botPat, gamma] ::=> [c]))
  ],
  uAbbrevs = [neg],
  bAbbrevs = [iff]
  }

--------------------------------------------------------------------------------
-- Linear logic

-- From "A taste of linear logic", Wadler.

-- connectives

-- Intuitionistic and linear assumptions. Linear assumptions are the default, so we
-- just provide a unary op indicating that an assumption is intuitionistic. This is
-- like Wadler's [] notation, but we'll use ^ instead of brackets.

intPat = UnaryOpPat (UniName ("*","*"))

-- unary operators
ofCoursePat = UnaryOpPat (UniName ("!","!"))

-- binary operators
lolPat = BinaryOpPat (UniName ("-o", "⊸"))
timesPat = BinaryOpPat (UniName ("x", "⊗"))
plusPat = BinaryOpPat (UniName ("+", "⊕"))
-- we also use andPat, above.

-- wll, or Wadler's linear logic.
wll :: Calculus
wll = Calculus
  { calcName = "wll"
  , axioms = [ ("Id",  [a] ::=> [a])
             , ("*Id", [intPat a] ::=> [a])]
  , rules =
    [ ("!I",  ([[intPat gamma] ::=> [a]]
              , [intPat gamma] ::=> [ofCoursePat a]))
    , ("!E",  ([[gamma] ::=> [ofCoursePat a], [delta, intPat a] ::=> [b]]
              , [gamma, delta] ::=> [b]))
    , ("-oI", ([[gamma, a] ::=> [b]]
              , [gamma] ::=> [a `lolPat` b]))
    , ("-oE", ([[gamma] ::=> [a `lolPat` b], [delta] ::=> [a]]
              , [gamma, delta] ::=> [b]))
    , ("xI",  ([[gamma] ::=> [a], [delta] ::=> [b]]
              , [gamma, delta] ::=> [a `timesPat` b]))
    , ("xE",  ([[gamma] ::=> [a `timesPat` b], [delta, a, b] ::=> [c]]
              , [gamma, delta] ::=> [c]))
    , ("&I",  ([[gamma] ::=> [a], [gamma] ::=> [b]]
              , [gamma] ::=> [a `andPat` b]))
    , ("&E1", ([[gamma] ::=> [a `andPat` b]]
              , [gamma] ::=> [a]))
    , ("&E2", ([[gamma] ::=> [a `andPat` b]]
              , [gamma] ::=> [b]))
    , ("+I1", ([[gamma] ::=> [a]]
              , [gamma] ::=> [a `plusPat` b]))
    , ("+I2", ([[gamma] ::=> [b]]
              , [gamma] ::=> [a `plusPat` b]))
    , ("+E",  ([[gamma] ::=> [a `plusPat` b], [delta, a] ::=> [c], [delta, b] ::=> [c]]
              , [gamma, delta] ::=> [c]))
    , ("Ctr", ([[gamma, intPat a, intPat a] ::=> [b]]
              , [gamma, intPat a] ::=> [b]))
    , ("Wk",  ([[gamma] ::=> [b]]
              , [gamma, intPat a] ::=> [b]))
    ]
  , uAbbrevs = []
  , bAbbrevs = []
  }
