module Data.FindCycle
  ( findCycleLenFloyd
  , findCycleFloyd
  , findCycleLenFloydL
  , findCycleFloydL) where

findCycleLenFloyd :: (Eq a) => (a -> a) -> a -> (Int, Int)
findCycleLenFloyd f a = findCycleLenFloydL (iterate f a)

findCycleFloyd :: (Eq a) => (a -> a) -> a -> ([a], [a])
findCycleFloyd f a = findCycleFloydL (iterate f a)

findCycleLenFloydL :: (Eq a) => [a] -> (Int, Int)
findCycleLenFloydL xs = detectCycle 0 xs xs
  where detectCycle n (t:ts) (_:h:hs)
          | t == h = findMu 0 xs ts
          | otherwise = detectCycle (n+1) ts hs
        detectCycle n _ [_] = (2*n+1, 0)
        detectCycle n _ _ = (2*n, 0)

        findMu mu (t:ts) (m:ms)
          | t == m = (mu, 1+findLambda m ms)
          | otherwise = findMu (mu+1) ts ms
        findMu mu _ _ = (mu, 0)

        findLambda m (x:xs')
          | m == x = 0
          | otherwise = 1+findLambda m xs'
        findLambda _ [] = 0

findCycleFloydL :: (Eq a) => [a] -> ([a], [a])
findCycleFloydL xs = (pre, take lambda cyc)
  where (mu, lambda) = findCycleLenFloydL xs
        (pre, cyc) = splitAt mu xs
