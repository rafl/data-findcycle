module Data.FindCycle
  ( CycleFinder
  , brent
  , floyd
  , nivash
  , findCycle
  , unsafeFromList
  , minimalMu
  , cached
  , extract
  ) where

import Data.List (uncons)
import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))

data Input a = FuncInput (a -> a) a | ListInput [a]

inpUncons :: Input a -> Maybe (a, Input a)
inpUncons (ListInput xs) = fmap ListInput <$> uncons xs
inpUncons (FuncInput f x) = Just (x, FuncInput f (f x))

inpAdvance :: Input a -> Int -> Input a
inpAdvance (ListInput xs) n = ListInput (drop n xs)
inpAdvance (FuncInput f x) n = FuncInput f (advance n x)
  where advance 0 a = a
        advance n' a = advance (n'-1) (f a)

newtype CycleFinder a r = CycleFinder { runCycleFinder :: Input a -> r }

brent :: (Eq a) => CycleFinder a (Int, Int)
brent = CycleFinder $ \s ->
  maybe (0, 0) (uncurry (findLambda 1 1)) (inpUncons s)
  where findLambda pow lambda t hs =
          maybe (pow+lambda-1, 0) (uncurry go) (inpUncons hs)
          where go h hs'
                  | t == h = (pow, lambda)
                  | pow == lambda = findLambda (2*pow) 1 h hs'
                  | otherwise = findLambda pow (1+lambda) t hs'

nivash :: (Ord a) => CycleFinder a (Int, Int)
nivash = CycleFinder $ go 0 []
  where go i stack st = maybe (i, 0) (uncurry go') (inpUncons st)
          where go' x st'
                  | (sx, si) : _ <- stack', sx == x = (si, i - si)
                  | otherwise = go (i + 1) ((x, i):stack') st'
                  where stack' = dropWhile ((> x) . fst) stack

floyd :: (Eq a) => CycleFinder a (Int, Int)
floyd = CycleFinder $ \s -> detectCycle 0 s s
  where detectCycle n ts hs =
          fromMaybe (2*n, 0) $
            go <$> inpUncons ts <*> (inpUncons . snd =<< skipped)
              <|> (2*n+1, 0) <$ skipped
          where skipped = inpUncons hs
                go (t, ts') (h, hs')
                  | t == h = (n, findLambda 1 t ts')
                  | otherwise = detectCycle (n+1) ts' hs'
        findLambda n m ms =
          maybe n (uncurry go) (inpUncons ms)
          where go x xs
                  | m == x = n
                  | otherwise = findLambda (n+1) m xs

findCycle :: CycleFinder a r -> (a -> a) -> a -> r
findCycle alg f x = runCycleFinder alg (FuncInput f x)

unsafeFromList :: CycleFinder a r -> [a] -> r
unsafeFromList alg = runCycleFinder alg . ListInput

cached :: CycleFinder a r -> CycleFinder a r
cached (CycleFinder alg) = CycleFinder cache
  where cache s@(ListInput _) = alg s
        cache (FuncInput f x) = alg (ListInput (iterate f x))

minimalMu :: (Eq a) => CycleFinder a (Int, Int) -> CycleFinder a (Int, Int)
minimalMu alg = CycleFinder $ \s -> maybeFindMu s (runCycleFinder alg s)
  where maybeFindMu s r@(_, lambda)
          | lambda == 0 = r
          | otherwise = (findMu 0 s (inpAdvance s lambda), lambda)
        findMu mu ts ms =
          fromMaybe mu $ go <$> inpUncons ts <*> inpUncons ms
          where go (t, ts') (m, ms')
                  | t == m = mu
                  | otherwise = findMu (mu+1) ts' ms'

extract :: (Eq a) => CycleFinder a (Int, Int) -> CycleFinder a ([a],[a])
extract alg = CycleFinder $ \s -> extractList s (runCycleFinder alg s)
  where extractList s (mu, lambda) = take lambda <$> splitAt mu (gatherAll s)
        gatherAll (ListInput xs) = xs
        gatherAll (FuncInput f x) = iterate f x
