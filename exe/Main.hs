{-# LANGUAGE OverloadedStrings #-}

module Main where
import Brick
    ( forceAttrMap,
      halt,
      txt,
      defaultMain,
      str,
      AttrMap,
      EventM,
      Next,
      BrickEvent,
      CursorLocation,
      App(..),
      Widget,
      hBox,
      hLimitPercent,
      padLeftRight,
      vBox )
import Graphics.Vty.Attributes ( defAttr )
import Control.Monad (void)
import qualified Data.Text as T
import Logix.Pretty (ppSimpleSequent)
import Logix.Types
    ( Op(Implies),
      Formula(OpFormula, PredFormula),
      SimpleSequent,
      Calculus(calcRules),
      SimpleCalculus,
      (|-) )
import Prettyprinter ( align, indent, vcat, Pretty(pretty), Doc )
import qualified Prettyprinter as P
import Brick.Widgets.Center ( center )
import Brick.Widgets.Border (hBorder, vBorder, border)
import Brick.Widgets.Border.Style (ascii, unicode)
import Data.Text (Text)
import Logix (g3c)

ui :: Widget ()
ui = str "Hello, world!"

main :: IO ()
main = void $ defaultMain logixApp s
    where s = LogixState (Derivation peirce []) g3c []
          peirce = [] |- [((p --> q) --> p) --> p]
          p = PredFormula "p" []
          q = PredFormula "q" []
          x --> y = OpFormula Implies [x, y]

data Derivation = Derivation SimpleSequent [(Text, Derivation)]
  deriving (Show)

ppDerivation :: Derivation -> Doc ann
ppDerivation (Derivation goal []) = ppSimpleSequent goal
ppDerivation (Derivation goal [(_,d)]) =
    vcat [ ppSimpleSequent goal
         , ppDerivation d ]
ppDerivation (Derivation goal ds) =
    vcat [ ppSimpleSequent goal
         , indent 2 (align (vcat (ppDerivation . snd <$> ds))) ]

data LogixState = LogixState { derivation :: Derivation
                             , calculus :: SimpleCalculus
                             , goal :: [Int] -- ^ pointer into the derivation
                             }

getSubgoal :: [Int] -> Derivation -> SimpleSequent
getSubgoal [] (Derivation sequent _) = sequent
getSubgoal (i:is) (Derivation _ ds) = getSubgoal is (snd (ds !! i))

data LogixResource = LogixResource
    deriving (Eq, Show, Ord)

logixApp :: App LogixState e LogixResource
logixApp = App
    { appDraw = logixDraw
    , appChooseCursor = logixChooseCursor
    , appHandleEvent = logixHandleEvent
    , appStartEvent = logixStartEvent
    , appAttrMap = logixAttrMap
    }

logixDraw :: LogixState -> [Widget LogixResource]
logixDraw s = [
                center (hBox [ border $ hLimitPercent 50 $ center $ derivationWidget s
                             , padLeftRight 3 $ rulesWidget s
                             ])]

derivationWidget :: LogixState -> Widget LogixResource
derivationWidget (LogixState d _ _) = txt (T.pack (show (ppDerivation d)))

rulesWidget :: LogixState -> Widget LogixResource
rulesWidget (LogixState d calc g) =
    let goal = getSubgoal g d
        applications = [ (ruleName, application)
                       | (ruleName, rule) <- calcRules calc
                       , application <- rule goal]
    in vBox (applicationWidget <$> zip [1..] applications)

applicationWidget :: (Integer, (T.Text, [SimpleSequent])) -> Widget LogixResource
applicationWidget (i, (ruleName, subgoals)) =
    txt $ T.pack $ show $
    vcat [ pretty i <> "." P.<+> pretty ruleName
         , indent 2 $ align $ vcat $ ppSimpleSequent <$> subgoals ]

logixChooseCursor :: LogixState -> [CursorLocation LogixResource] -> Maybe (CursorLocation LogixResource)
logixChooseCursor s _ = Nothing

logixHandleEvent :: LogixState -> BrickEvent LogixResource e -> EventM LogixResource (Next LogixState)
logixHandleEvent s _ = halt s

logixStartEvent :: LogixState -> EventM LogixResource LogixState
logixStartEvent s = return s

logixAttrMap :: LogixState -> AttrMap
logixAttrMap s = forceAttrMap defAttr
