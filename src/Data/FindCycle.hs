{-# LANGUAGE BangPatterns, RecordWildCards #-}

module Data.FindCycle
  ( findCycleLenBrent
  , findCycleBrent
  , findCycleLenBrentL
  , findCycleBrentL
  , findCycleLenFloyd
  , findCycleFloyd
  , findCycleLenFloydL
  , findCycleFloydL) where

import Data.Maybe (fromMaybe)
import Data.List (uncons)
import Control.Applicative ((<|>))

data Input s a = Input { inpUncons :: s -> Maybe (a, s)
                       , inpAdvance :: Int -> s -> s }

funcInput :: (a -> a) -> Input a a
funcInput f = Input (\x -> Just (x, f x)) advance
  where advance 0 !a = a
        advance n !a = advance (n-1) (f a)

listInput :: Input [a] a
listInput = Input uncons drop

{-# INLINE brentLenGeneric #-}
{-# SPECIALIZE brentLenGeneric :: (Eq a) => Input a a -> a -> (Int, Int) #-}
{-# SPECIALIZE brentLenGeneric :: (Eq a) => Input [a] a -> [a] -> (Int, Int) #-}
brentLenGeneric :: (Eq a) => Input s a -> s -> (Int, Int)
brentLenGeneric Input{..} s =
  maybe (0, 0) (uncurry (findLambda 1 1)) (inpUncons s)
  where findLambda !pow !lambda t hs =
          maybe (pow+lambda-1, 0) (uncurry go) (inpUncons hs)
          where go h hs'
                  | t == h = (findMu 0 s (inpAdvance lambda s), lambda)
                  | pow == lambda = findLambda (2*pow) 1 h hs'
                  | otherwise = findLambda pow (1+lambda) t hs'
        findMu !mu ts ms =
          fromMaybe mu $ go <$> inpUncons ts <*> inpUncons ms
          where go (t, ts') (m, ms')
                  | t == m = mu
                  | otherwise = findMu (mu+1) ts' ms'

findCycleLenBrent :: (Eq a) => (a -> a) -> a -> (Int, Int)
findCycleLenBrent f = brentLenGeneric (funcInput f)

findCycleBrent :: (Eq a) => (a -> a) -> a -> ([a], [a])
findCycleBrent f a = findCycleBrentL (iterate f a)

findCycleLenBrentL :: Eq a => [a] -> (Int, Int)
findCycleLenBrentL = brentLenGeneric listInput

findCycleBrentL :: (Eq a) => [a] -> ([a], [a])
findCycleBrentL xs = (pre, take lambda cyc)
  where (mu, lambda) = findCycleLenBrentL xs
        (pre, cyc) = splitAt mu xs

{-# INLINE floydLenGeneric #-}
{-# SPECIALIZE floydLenGeneric :: (Eq a) => Input a a -> a -> (Int, Int) #-}
{-# SPECIALIZE floydLenGeneric :: (Eq a) => Input [a] a -> [a] -> (Int, Int) #-}
floydLenGeneric :: (Eq a) => Input s a -> s -> (Int, Int)
floydLenGeneric Input{..} s = detectCycle 0 s s
  where detectCycle !n ts hs =
          fromMaybe (2*n, 0) $
            go <$> inpUncons ts <*> (inpUncons . snd =<< skipped)
              <|> (2*n+1, 0) <$ skipped
          where skipped = inpUncons hs
                go (t, ts') (h, hs')
                  | t == h = findMu 0 s ts'
                  | otherwise = detectCycle (n+1) ts' hs'

        findMu !mu ts ms = fromMaybe (mu, 0) $ go <$> inpUncons ts <*> inpUncons ms
          where go (t, ts') (m, ms')
                  | t == m = (mu, findLambda 1 m ms')
                  | otherwise = findMu (mu+1) ts' ms'

        findLambda !n m ms =
          maybe n (uncurry go) (inpUncons ms)
          where go x xs
                  | m == x = n
                  | otherwise = findLambda (n+1) m xs

findCycleLenFloyd :: (Eq a) => (a -> a) -> a -> (Int, Int)
findCycleLenFloyd f = floydLenGeneric (funcInput f)

findCycleFloyd :: (Eq a) => (a -> a) -> a -> ([a], [a])
findCycleFloyd f a = findCycleFloydL (iterate f a)

findCycleLenFloydL :: (Eq a) => [a] -> (Int, Int)
findCycleLenFloydL = floydLenGeneric listInput

findCycleFloydL :: (Eq a) => [a] -> ([a], [a])
findCycleFloydL xs = (pre, take lambda cyc)
  where (mu, lambda) = findCycleLenFloydL xs
        (pre, cyc) = splitAt mu xs
