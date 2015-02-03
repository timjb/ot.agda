module Main where

import Data.List (group)
import Data.Maybe (catMaybes)
import Data.Monoid ((<>))
import Control.Monad (forM_)

data Action = Noop | InsertChar | RetainChar | DeleteChar | InsertTombstone | RetainTombstone
  deriving (Show, Eq, Ord, Enum, Bounded)

renderAction :: Action -> String -> String -> String
renderAction Noop _ _ = "Noop"
renderAction InsertChar var1 var2 = "(InsertChar " <> var2 <> " " <> var1 <> ")"
renderAction action var1 _ = "(" <> show action <> " " <> var1 <> ")"

maybeRenderAction :: Maybe Action -> String -> String -> String
maybeRenderAction Nothing var1 _ = var1
maybeRenderAction (Just action) var1 var2 = renderAction action var1 var2

data State = Char | Tombstone | End deriving (Eq, Show)

startState :: Action -> Maybe State
startState Noop = Just End
startState InsertChar = Nothing
startState RetainChar = Just Char
startState DeleteChar = Just Char
startState InsertTombstone = Nothing
startState RetainTombstone = Just Tombstone

cong :: String -> Maybe Action -> Maybe Action -> Maybe Action -> String
cong fun x y z =
  "cong " <> fun <> " (transformAssociative "
    <> maybeRenderAction x "x" "s" <> " "
    <> maybeRenderAction y "y" "t" <> " "
    <> maybeRenderAction z "z" "u" <> ")"

transformAssociative :: Action -> Action -> Action -> String
transformAssociative InsertChar y z =
  cong "(xInsertChar s)" Nothing (Just y) (Just z)
transformAssociative InsertTombstone y z =
  cong "xInsertTombstone" Nothing (Just y) (Just z)
transformAssociative x InsertChar z =
  cong "(yInsertChar t)" (Just x) Nothing (Just z)
transformAssociative x InsertTombstone z =
  cong "yInsertTombstone" (Just x) Nothing (Just z)
transformAssociative x y InsertChar =
  cong "(zInsertChar u)" (Just x) (Just y) Nothing
transformAssociative x y InsertTombstone =
  cong "zInsertTombstone" (Just x) (Just y) Nothing
transformAssociative RetainChar RetainChar RetainChar =
  cong "xyzRetainChar" Nothing Nothing Nothing
transformAssociative RetainTombstone RetainTombstone RetainTombstone =
  cong "xyzRetainTombstone" Nothing Nothing Nothing
transformAssociative DeleteChar RetainChar RetainChar =
  cong "xDeleteYzRetainChar" Nothing Nothing Nothing
transformAssociative RetainChar DeleteChar RetainChar =
  cong "yDeleteXzRetainChar" Nothing Nothing Nothing
transformAssociative RetainChar RetainChar DeleteChar =
  cong "zDeleteXyRetainChar" Nothing Nothing Nothing
transformAssociative DeleteChar DeleteChar RetainChar =
  cong "xyDeleteZRetainChar" Nothing Nothing Nothing
transformAssociative DeleteChar RetainChar DeleteChar =
  cong "xzDeleteYRetainChar" Nothing Nothing Nothing
transformAssociative RetainChar DeleteChar DeleteChar =
  cong "yzDeleteXRetainChar" Nothing Nothing Nothing
transformAssociative DeleteChar DeleteChar DeleteChar =
  cong "xyzDeleteChar" Nothing Nothing Nothing
transformAssociative Noop Noop Noop =
  "refl"

triples :: [(Action, Action, Action)]
triples = filter isConsistent rawTriples
  where
    states = [minBound..maxBound]
    rawTriples = do
      x <- states
      y <- states
      z <- states
      return (x,y,z)
    isConsistent (x,y,z) =
      length (group $ catMaybes $ map startState [x,y,z]) <= 1

main :: IO ()
main = do
  forM_ triples $ \(x, y, z) -> do
    putStrLn $ "transformAssociative " <>
      renderAction x "x" "s" <> " " <>
      renderAction y "y" "t" <> " " <>
      renderAction z "z" "u" <> " ="
    putStrLn $ "  " <> transformAssociative x y z
