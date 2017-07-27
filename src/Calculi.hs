module Calculi where

import Calculus

-- To add your own calculus to logix, define it under the "Calculi definitions"
-- section, and add it to the following list:

calculi :: [Calculus]
calculi = [g3ip, g3cp, g0ip, g0ip_em, g3ipm, hilbert]

--------------------------------------------------------------------------------
-- Calculi definitions

atom = AtomPat "P"
a = VarPat "A"
b = VarPat "B"
c = VarPat "C"
gamma = SetPat "Gamma"
delta = SetPat "Delta"

-- | G3ip, a contraction-free calculus for intuitionistic logic with shared
-- contexts. A good calculus for proof search of intuitionistic formulas.
g3ip :: Calculus
g3ip = Calculus {
  name = "g3ip",
  axioms = [("Axiom", [atom, gamma] ::=> [atom])],
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

-- | G0ip, a calculus for intuitionistic logic with independent contexts. Not a great
-- calculus for proof search due to the independent contexts, and the fact that we
-- usually need to explicitly use weakening and/or contraction in order to prove
-- simple formulas.
g0ip :: Calculus
g0ip = Calculus {
  name = "g0ip",
  axioms = [("Axiom", [atom] ::=> [atom])],
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

-- | G0ip with the law of excluded middle, so a classical sequent calculus with
-- independent contexts.
g0ip_em :: Calculus
g0ip_em = Calculus {
  name = "g0ip_em",
  axioms = [("Axiom", [atom] ::=> [atom])],
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
  , ("EM", ([ [atom, gamma] ::=> [c], [negpat atom, delta] ::=> [c] ],
            [gamma, delta] ::=> [c]))
  , ("Wk", ([ [gamma] ::=> [c] ],
            [a, gamma] ::=> [c]))
  , ("Ctr", ([ [a, a, gamma] ::=> [c] ],
             [a, gamma] ::=> [c]))
  ]}

-- | G3cp, a contraction-free calculus for classical logic with shared contexts. This
-- calculus is ideally suited for proof search, as any given sequent usually has at
-- most one rule that applies to it.
g3cp :: Calculus
g3cp = Calculus {
  name = "g3cp",
  axioms = [("Axiom", [atom, gamma] ::=> [delta, atom])],
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

g3ipm :: Calculus
g3ipm = Calculus {
  name = "g3ipm",
  axioms = [("Axiom", [atom, gamma] ::=> [delta, atom])],
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

hilbert :: Calculus
hilbert = Calculus {
  name = "hilbert",
  axioms = [("H1", [] ::=> [a $> (b $> a)]),
            ("H2",  [] ::=> [(a $> b) $> ((a $> (b $> c)) $> (a $> c))]),
            ("H3", [] ::=> [negpat (negpat a) $> a])],
  rules = [("MP", ([ [] ::=> [a], [] ::=> [a $> b] ],
                   [] ::=> [b]))]
}
