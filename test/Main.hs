{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Test.QuickCheck
import System.Exit
import Control.Monad
import Data.FindCycle

prop_FloydLenL_nocycle :: NonNegative Int -> Property
prop_FloydLenL_nocycle (NonNegative n) = findCycleLenFloydL [1..n] === (n, 0)

prop_FloydLenL_cycle :: NonNegative Int -> Positive Int -> Property
prop_FloydLenL_cycle (NonNegative a) (Positive b) =
  findCycleLenFloydL ([1..a] ++ cycle [a+1 .. a+b]) === (a, b)

prop_FloydL_nocycle :: NonNegative Int -> Property
prop_FloydL_nocycle (NonNegative n) = findCycleFloydL xs === (xs, [])
  where xs = [1..n]

prop_FloydL_cycle :: NonNegative Int -> Positive Int -> Property
prop_FloydL_cycle (NonNegative a) (Positive b) =
  findCycleFloydL (as ++ cycle bs) === (as, bs)
  where as = [1..a]
        bs = [a+1..a+b]

prop_FloydLen_id :: Int -> Property
prop_FloydLen_id n = findCycleLenFloyd id n === (0, 1)

prop_FloydLen_mod :: Int -> Positive Int -> Property
prop_FloydLen_mod a (Positive b) =
  findCycleLenFloyd (\x -> (x+1) `mod` b) (a `mod` b) === (0, b)

$(return [])

main :: IO ()
main = $(quickCheckAll) >>= (`unless` exitFailure)
