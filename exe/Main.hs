{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

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
      BrickEvent (..),
      CursorLocation,
      App(..),
      Widget,
      hBox,
      hLimitPercent,
      padLeftRight,
      vBox, padBottom, Padding (..), clickable, getVtyHandle, padLeft )
import Graphics.Vty.Attributes ( defAttr )
import Control.Monad (void, when)
import qualified Data.Text as T
import Logix.Calculi
import Logix.Types
import Prettyprinter ( align, indent, vcat, Pretty(pretty), Doc )
import qualified Prettyprinter as P
import Brick.Widgets.Center ( center )
import Brick.Widgets.Border (hBorder, vBorder, border)
import Brick.Widgets.Border.Style (ascii, unicode)
import Data.Text (Text)
import Graphics.Vty (Event(..), Key (..), Button (..), Vty (..), Output (..), Mode (..))
import Brick.Main (continue)
import Lens.Micro
import Lens.Micro.TH (makeLenses)
import Control.Monad.IO.Class (MonadIO(..))

listApplications :: ClassicalCalculus -> ClassicalSequent -> [(Int, (Text, [ClassicalSequent]))]
listApplications calc sequent =
    let applications = [ (ruleName, application)
                       | (ruleName, arity, rule) <- calcRules calc
                       , application <- rule sequent []]
    in zip [1..] applications

data Derivation = 
    Derivation { _conclusion :: ClassicalSequent
               , _subDerivations :: Maybe (Text, [Derivation])
               , _subgoalId :: [Int]
               }
    deriving (Show)

makeLenses ''Derivation

data LogixState = LogixState { _derivation :: Derivation
                             , _calculus :: ClassicalCalculus
                             , _goal :: [Int] -- ^ pointer into the derivation
                             , _applicableRuleList :: [(Int, (Text, [ClassicalSequent]))]
                             -- ^ List of all applicable rules at current subgoal
                             }

makeLenses ''LogixState

changeGoal :: [Int] -> LogixState -> LogixState
changeGoal is s =
    let Derivation sequent _ _ = getSubgoal is (s ^. derivation)
    in s & goal .~ is
         & applicableRuleList .~ listApplications (s ^. calculus) sequent

getSubgoal :: [Int] -> Derivation -> Derivation
getSubgoal [] d = d
getSubgoal _ d@(Derivation _ Nothing _) = d
getSubgoal (i:is) (Derivation _ (Just (_, ds)) _) = getSubgoal is (ds !! (i-1))

expandDerivation :: [Int] -> Text -> [Derivation] -> Derivation -> Derivation
expandDerivation [] ruleName subDers (Derivation sequent _ subgoalId) =
    Derivation sequent (Just (ruleName, subDers)) subgoalId
expandDerivation (_:_) _ _ d@(Derivation _ Nothing _) = d
expandDerivation (i:is) ruleName subDers (Derivation sequent (Just (r, ds)) subgoalId) =
    let subDers' = ds & ix (i-1) %~ expandDerivation is ruleName subDers
    in Derivation sequent (Just (r, subDers')) subgoalId

data LogixResource = ApplicationWidget Int
                   | Subgoal [Int]
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
logixDraw s = 
    [ center (hBox [ border $ hLimitPercent 50 $ center $ derivationWidget (s ^. derivation)
                   , padLeftRight 3 $ rulesWidget s
                   ])]

derivationWidget :: Derivation -> Widget LogixResource
derivationWidget (Derivation sequent mSubDers subgoalId) =
    clickable (Subgoal subgoalId) $ case mSubDers of
        Nothing -> txt (T.pack (show (ppClassicalSequent sequent)))
        Just (_, []) -> txt (T.pack (show (ppClassicalSequent sequent)))
        Just (_, subDers) -> 
          vBox [ txt (T.pack (show (ppClassicalSequent sequent)))
               , padLeft (Pad 2) $ vBox $ derivationWidget <$> subDers
               ]
    -- txt (T.pack (show (ppDerivation d)))

rulesWidget :: LogixState -> Widget LogixResource
rulesWidget (LogixState d calc g applications) =
    let goal = getSubgoal g d
        header = padBottom (Pad 1) $ txt (T.pack (show g))
    in vBox (header : (applicationWidget <$> applications))

applicationWidget :: (Int, (T.Text, [ClassicalSequent])) -> Widget LogixResource
applicationWidget (i, (ruleName, subgoals)) =
    clickable (ApplicationWidget i) $
    padBottom (Pad 1) $ txt $ T.pack $ show $
    vcat [ pretty i <> "." P.<+> pretty ruleName
         , indent 2 $ align $ vcat $ 
           ppClassicalSequent <$> subgoals ]

logixChooseCursor :: LogixState -> [CursorLocation LogixResource] -> Maybe (CursorLocation LogixResource)
logixChooseCursor s _ = Nothing

logixHandleEvent :: LogixState -> BrickEvent LogixResource e -> EventM LogixResource (Next LogixState)
logixHandleEvent s e = case e of
    VtyEvent (EvKey (KChar 'q') []) -> halt s
    MouseDown (ApplicationWidget i) _ _ _ -> do
        let Just (ruleName, premises') = lookup i (s ^. applicableRuleList)
            subDers' = [ Derivation p Nothing (s ^. goal ++ [i])
                       | (i, p) <- zip [1..] premises']
        continue $ 
          s & derivation %~ expandDerivation (s ^. goal) ruleName subDers'
    MouseDown (Subgoal subgoalId) _ _ _-> 
        continue $ changeGoal subgoalId s
    _ -> continue s

logixStartEvent :: LogixState -> EventM LogixResource LogixState
logixStartEvent s = do
    vty <- getVtyHandle
    let output = outputIface vty
    when (supportsMode output Mouse) $
      liftIO $ setMode output Mouse True
    return s

logixAttrMap :: LogixState -> AttrMap
logixAttrMap s = forceAttrMap defAttr

main :: IO ()
main = do
    
    void $ defaultMain logixApp s
    where s = LogixState (Derivation sequent Nothing []) g3c [] (listApplications g3c sequent)
          sequent = [p .& q] |- [q .& p]
          p = PredFormula "p" []
          q = PredFormula "q" []
          x --> y = OpFormula Implies [x, y]
          x .& y = OpFormula And [x, y]
