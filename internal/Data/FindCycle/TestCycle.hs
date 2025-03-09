{-# LANGUAGE RecordWildCards #-}

module Data.FindCycle.TestCycle (
    Cycle(..)
) where

import Control.Applicative ((<*>))
import Data.Foldable (find)
import Data.Functor ((<$>))
import Data.Maybe
import Data.Numbers.Primes
import Test.QuickCheck
import Prelude hiding ((<$>), (<*>))

data Cycle = Cycle
    { cycMu, cycLambda :: Int
    , cycF :: Integer -> Integer
    , cycX0 :: Integer
    }

instance Show Cycle where
    show Cycle{..} = unwords ["Cycle", show cycMu, show cycLambda]

instance Arbitrary Cycle where
    arbitrary = do
        (Positive muPlusLambda) <- scaled smooth arbitrary
        mu <- choose (0, muPlusLambda - 1)
        let m = fromJust $ find (> fromIntegral muPlusLambda) primes
        -- TODO: just pick using Large suchThat mod m /= 0?
        let nonZeroModM = choose (1, m - 1)
        (f, x0) <- mkF mu (muPlusLambda - mu) m <$> nonZeroModM <*> nonZeroModM
        return (Cycle mu (muPlusLambda - mu) f x0)
      where
        scaled f g = sized $ \x -> resize (f x) g
        smooth s = max 1 (round $ (10 ** 5 :: Double) ** (fromIntegral s / 100))
        mkF mu lambda m a b = (f, g 0)
          where
            n = fromIntegral $ mu + lambda
            g i = (a * i + b) `mod` m
            f x
                | i < n - 1 = g (i + 1)
                | otherwise = g (fromIntegral mu)
              where
                i = (modInv a m * ((x - b) `mod` m)) `mod` m
        modInv 1 _ = 1
        modInv x y = (a * y + 1) `div` x
          where
            a = x - modInv (y `mod` x) x
