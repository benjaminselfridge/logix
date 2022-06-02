{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

module Logix where

import Logix.Types

import Data.Text (Text)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MSet
import Data.Splittable ( Splittable(decapitate) )
import Data.MultiSet.Extras ((<|))

g3c :: SimpleCalculus
g3c = Calculus
  { calcName = "G3c"
  , calcAxioms = [("Axiom", axiom)]
  , calcRules = [ ("L&", andL)
                , ("R&", andR)
                , ("L|", orL)
                , ("R|", orR)
                , ("L->", impL)
                , ("R->", impR)
                , ("L_|_", bottomL)
  ]
  }
  where axiom (ants :|- sucs) = or
            [p == p' | (p@(PredFormula _ _) , _) <- decapitate ants
                     , (p', _) <- decapitate sucs
                     , p == p']
        andL (ants :|- sucs) =
            [ [ a <| b <| ants' :|- sucs ]
            | (OpFormula And [a, b], ants') <- decapitate ants ]
        andR (ants :|- sucs) =
            [ [ ants :|- a <| sucs', ants :|- b <| sucs' ]
            | (OpFormula And [a, b], sucs') <- decapitate sucs ]
        orL (ants :|- sucs) =
            [ [ a <| ants' :|- sucs, b <| ants' :|- sucs ]
            | (OpFormula Or [a, b], ants') <- decapitate ants ]
        orR (ants :|- sucs) =
            [ [ ants :|- a <| b <| sucs' ]
            | (OpFormula Or [a, b], sucs') <- decapitate sucs ]
        impL (ants :|- sucs) =
            [ [ ants' :|- a <| sucs, b <| ants' :|- sucs ]
            | (OpFormula Implies [a, b], ants') <- decapitate ants ]
        impR (ants :|- sucs) =
            [ [ a <| ants :|- b <| sucs' ]
            | (OpFormula Implies [a, b], sucs') <- decapitate sucs ]
        bottomL (ants :|- _) =
            [ [] | (OpFormula Bottom [], _) <- decapitate ants ]