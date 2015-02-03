module Main where

import Control.Monad (forM_)
import Data.Monoid ((<>))

data Action = Noop | InsertChar | RetainChar | DeleteChar | InsertTombstone | RetainTombstone
  deriving (Show, Eq, Ord)

renderAction :: Action -> String -> String -> String
renderAction Noop _ _ = "Noop"
renderAction InsertChar var1 var2 = "(InsertChar " <> var2 <> " " <> var1 <> ")"
renderAction action var1 _ = "(" <> show action <> " " <> var1 <> ")"

data State = Char | Tombstone | End deriving (Eq, Show)

data Side = L | R deriving (Eq, Show)

type Pair = ((Action, Action), (Action, Maybe Action))

pairs :: Maybe State -> [Pair]
pairs (Just Char) =
  [ ((RetainChar, RetainChar), (RetainChar, Nothing))
  , ((RetainChar, DeleteChar), (DeleteChar, Nothing))
  , ((DeleteChar, RetainTombstone), (DeleteChar, Nothing))
  , ((RetainChar, InsertChar), (InsertChar, Just RetainChar))
  , ((RetainChar, InsertTombstone), (InsertTombstone, Just RetainChar))
  , ((DeleteChar, InsertChar), (InsertChar, Just DeleteChar))
  , ((DeleteChar, InsertTombstone), (InsertTombstone, Just DeleteChar))
  ]
pairs (Just Tombstone) =
  [ ((RetainTombstone, RetainTombstone), (RetainTombstone, Nothing))
  , ((RetainTombstone, InsertChar), (InsertChar, Just RetainTombstone))
  , ((RetainTombstone, InsertTombstone), (InsertTombstone, Just RetainTombstone))
  ]
pairs (Just End) =
  [ ((Noop, InsertChar), (InsertChar, Just Noop))
  , ((Noop, InsertTombstone), (InsertTombstone, Just Noop))
  , ((Noop, Noop), (Noop, Just Noop))
  ]
pairs Nothing =
  [ ((InsertChar, DeleteChar), (InsertTombstone, Nothing))
  , ((InsertTombstone, RetainTombstone), (InsertTombstone, Nothing))
  , ((InsertChar, RetainChar), (InsertChar, Nothing))
  , ((InsertChar, InsertChar), (InsertChar, Just InsertChar))
  , ((InsertChar, InsertTombstone), (InsertTombstone, Just InsertChar))
  , ((InsertTombstone, InsertChar), (InsertChar, Just InsertTombstone))
  , ((InsertTombstone, InsertTombstone), (InsertTombstone, Just InsertTombstone))
  ]

data Handled = LS | RS | BS -- left side / right side / both sides

type Handler = Pair -> Pair -> String

handle :: String -> Handled -> Handler
handle congFun handled pairX pairY =
  "cong " <> congFun <> " (composeTransformCommutes " <>
  getXs pairX "x₁" "x₂" "c₁" "c₂" <> " " <> getYs pairY "y₁" "y₂" "d₁" "d₂" <> ")"
  where
    getFull :: Pair -> String -> String -> String -> String -> String
    getFull ((a1, a2), _) var1 var2 var3 var4 =
      renderAction a1 var1 var3 <> " " <> renderAction a2 var2 var4
    getHandled :: Pair -> String -> String -> String -> String -> String
    getHandled (_, (_, Nothing)) var1 var2 _ _ = var1 <> " " <> var2
    getHandled (_, (_, Just a)) var1 var2 var3 _ = renderAction a var1 var3 <> " " <> var2
    (getXs, getYs) = case handled of
      LS -> (getHandled, getFull)
      RS -> (getFull, getHandled)
      BS -> (getHandled, getHandled)

transform :: Action -> Action -> Handler
transform InsertChar a = \pairX pairY ->
  case pairX of
    (_, (_, Nothing)) -> handle "(insertCharDiamond₁ c₁)" LS pairX pairY
    (_, (_, Just _)) -> handle "(insertCharDiamond₁ c₂)" LS pairX pairY
transform InsertTombstone a = handle "insertTombstoneDiamond₁" LS
transform a InsertChar = \pairX pairY ->
  case pairY of
    (_, (_, Nothing)) -> handle "(insertCharDiamond₂ d₁)" RS pairX pairY
    (_, (_, Just _)) -> handle "(insertCharDiamond₂ d₂)" RS pairX pairY
transform a InsertTombstone = handle "insertTombstoneDiamond₂" RS
transform RetainChar RetainChar = handle "retainCharDiamond" BS
transform RetainTombstone RetainTombstone = handle "retainTombstoneDiamond" BS
transform DeleteChar RetainChar = handle "deleteCharDiamond₁" BS
transform RetainChar DeleteChar = handle "deleteCharDiamond₂" BS
transform DeleteChar DeleteChar = handle "deleteCharDiamond₃" BS
transform Noop Noop = const $ const "refl"

allCases :: [String]
allCases = do
  let states = [Just Char, Just Tombstone, Just End, Nothing]
  sx <- states
  sy <- maybe states (\s -> [Just s, Nothing]) sx
  px@((x1, x2), (xf, xl)) <- pairs sx
  py@((y1, y2), (yf, yl)) <- pairs sy
  return $ "composeTransformCommutes " <>
    renderAction x1 "x₁" "c₁" <> " " <>
    renderAction x2 "x₂" "c₂" <> " " <>
    renderAction y1 "y₁" "d₁" <> " " <>
    renderAction y2 "y₂" "d₂" <>
    " = \n  " <>
    transform xf yf px py

main :: IO ()
main = forM_ allCases putStrLn
