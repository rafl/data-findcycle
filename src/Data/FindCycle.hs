{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

{- |
  Module: Data.FindCycle
  Description: Find cycles in periodic functions (and lists)
  Copyright: (c) 2025 Florian Ragwitz
  License: MIT

  Any function @f :: a -> a@ where the type @a@ has finitely many values
  eventually has to be cyclic when iterated from some initial @a@.

  This module provides a number of common algorithms and utilities to identify
  and work with such cycles.
-}
module Data.FindCycle (
    -- * Typical Usage

    {- |
       The value of iterating @someCyclicFunc@ for \(10^{100}\) times from
       @startingValue@, using the 'brent' algorithm for cycle detection:

       > let fastCyclicFunc = cycleExp brent someCyclicFunc startingValue
       > fastCyclicFunc (10^100)

       The length of the non-repeating prefix and the length of the cycle, as
       determined using the 'nivash' algorithm:

       > let (mu, lambda) = findCycle nivash someCyclicFunc startingValue

       The same two lengths, plus two lists containing the values of the prefix and
       cyclic parts of the sequence using the 'naiveOrd' algorithm:

       > let (mu, lambda, (pre, cyc)) = findCycleExtract naiveOrd someCyclicFunc startingValue

       When you already have a list of values created by iterating a cyclic
       function:

       > let xs = iterate someCyclicFunc startingValue
       > let (mu, lambda, (pre, cyc)) = unsafeFindCycleFromList brent xs
    -}

    -- * CycleFinder type
    CycleFinder,

    -- * Algorithms

    {- |
       Cycles are typically described with a pair \((\mu, \lambda)\), where
       \(\mu\) represents the length of the non-cyclic prefix of the sequence, and
       \(\lambda\) represents the length of the repeating cycle of the sequence.

       The cycle finding algorithms provided by this module return such a pair as
       a result, but some might return an upper bound \(\tilde{\mu}\) instead of
       the minimal \(\mu\) in order to avoid the computational cost of finding the
       minimal value. This approximation is acceptable in many practical cases,
       such as when using 'cycleExp', which uses the cyclic behavior of a function
       to efficiently compute \(f^n(x)\) for large \(n\).

       When a minimal \(\mu\) is needed, it can be computed from a t'CycleFinder'
       returning a non-minimal \(\tilde{\mu}\) using 'minimalMu'.

       All algorithms always provide a minimal \(\lambda\) as opposed to a
       multiple of the true cycle length.

       In practice, you'll usually want to use 'nivash', 'brent', or one of the
       naive variants. If performance matters and you're not sure what to choose,
       compare the alternatives by benchmarking for your usecase.
    -}

    -- ** Naive

    {- |
       These algorithms use Map-like structures to store the index of the first
       occurrence of each value in the sequence until a duplicate is found.

       They always produce the minimal \((\mu, \lambda)\).

       They never iterate the sequence further than \(\mu + \lambda\) elements.

       They never compute an element at a given position in the sequence more than
       once.

       They use memory approximately proportional to \(\mu + \lambda\).

       'naiveHashable' tends to perform slightly better and uses slightly less
       memory. Both are provided for completeness and for cases where you might
       not have a 'Hashable' instance or don't want to write one.
    -}
    naiveOrd,
    naiveHashable,

    -- ** Constant Memory

    {- |
       These algorithms use a constant amount of memory, at the cost of having to
       potentially evaluate values in the sequence more than once.

       'brent' is always better than 'floyd', and the latter is only present for
       completeness and as a baseline for testing. You shouldn't use 'floyd'.

       They always compute a minimal \(\lambda\), but only an upper bound
       \(\tilde{\mu}\) for the cycle length. Combine with 'minimalMu' if the
       minimal \(\mu\) is needed.
    -}
    brent,
    floyd,

    -- ** Memory/Time Compromise
    nivash,

    -- * Running algorithms
    findCycle,
    findCycleExtract,
    cycleExp,
    cycleExp',
    unsafeFindCycleFromList,

    -- * Utilities
    minimalMu,
) where

import Control.Applicative ((<|>))
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable)
import Data.List (uncons)
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, fromMaybe)

data Input s a = Input
    { inpUncons :: s -> Maybe (a, s)
    , inpAdvance :: Int -> s -> s
    }

funcInput :: (a -> a) -> Input a a
funcInput f = Input (\x -> Just (x, f x)) advance
  where
    advance 0 a = a
    advance n a = advance (n - 1) (f a)

listInput :: Input [a] a
listInput = Input uncons drop

{- |
  An algorithm to find the cycle in a function from @a@ to @a@ (or a list of @a@s).
-}
newtype CycleFinder a = CycleFinder
    { runCycleFinder :: forall s. Input s a -> s -> (Int, Int)
    }

{- |
  Runs a t'CycleFinder' algorithm for the given function and starting value,
  returning a pair \((\mu, \lambda)\) representing the length of the
  non-cyclic prefix and the length of the cycle of the sequence.
-}
findCycle :: CycleFinder a -> (a -> a) -> a -> (Int, Int)
findCycle alg f = runCycleFinder alg (funcInput f)

extract :: Int -> Int -> [a] -> ([a], [a])
extract mu lambda = fmap (take lambda) . splitAt mu

{- |
  Like 'findCycle', but also returns a third value @(pre, cyc)@ such that

  > pre ++ cycle cyc == iterate f x

  In addition to extracting the prefix and cyclic part of the list, this can
  also be used to cache some function calls to @f@ which the specified
  t'CycleFinder' might make, as the results of all calls to @f@ in the sequence
  are memorised in a lazy list which is later used to extract @pre@ and @cyc@.

  If you're only interested in caching calls to @f@ but don't need the two
  parts of the list, just don't evaluate the last part of the return value to
  not pay the cost of those parts being computed.
-}
findCycleExtract :: CycleFinder a -> (a -> a) -> a -> (Int, Int, ([a], [a]))
findCycleExtract alg f x = (mu, lambda, extract mu lambda xs)
  where
    xs = iterate f x
    (mu, lambda) = runCycleFinder alg listInput xs

{- |
  Runs the t'CycleFinder' for a given input list.

  This function is provided as a convenience for when you already have a list
  of values you'd like to find a cycle in. It's referred to as "unsafe", because
  it might lead to surprising results when the input doesn't satisfy the
  invariants that different algorithms assume.

  All algorithms assume that the sequence they're searching can be constructed
  by repeated function application from a starting value. Many sequences can't
  be, such as @[1,2,1,3,1,4,1,5,...]@ (because there can only be one unique
  successor of @1@).

  Algorithms also assume the input sequence to be infinite, and they will
  commonly consume more than \(\mu + \lambda\) (or \(\tilde{\mu} + \lambda\))
  elements from it. If you provide a finite input list, cycles might not be
  identified correctly if the chosen algorithm runs into the end of it, even
  though the input does technically contain an identifiable cycle.

  If an assumption is violated, algorithms might wrongly identify cycles or
  never terminate. Try to stick to 'findCycle', 'findCycleExtract', 'cycleExp',
  or 'cycleExp'' if possible, or only pass infinite lists generated via
  @iterate f x@ (or equivalent) to 'unsafeFindCycleFromList'.

  Similar to 'findCycleExtract', just don't evaluate the last part of the
  return value if you don't need it and want to avoid the cost of computing it.
-}
unsafeFindCycleFromList :: CycleFinder a -> [a] -> (Int, Int, ([a], [a]))
unsafeFindCycleFromList alg xs = (mu, lambda, extract mu lambda xs)
  where
    (mu, lambda) = runCycleFinder alg listInput xs

{-# INLINE cycleExpWith #-}
cycleExpWith :: CycleFinder a -> Input s a -> s -> Integer -> a
cycleExpWith alg inp@Input{..} s n =
    fst . fromJust . inpUncons $ inpAdvance (fromIntegral ix) s
  where
    (mu, lambda) = runCycleFinder alg inp s
    (mu', lambda') = (fromIntegral mu, fromIntegral lambda)
    ix
        | n < mu' = n
        | otherwise = mu' + ((n - mu') `mod` lambda')

{- |
  Constructs an efficient evaluator for a cyclic function by "exponentiating" it.
  Given a t'CycleFinder' for a function @f@ and an initial value @x@, it returns
  a function of type @Integer -> a@ which computes the nth iterate (i.e. the
  value of \(f^n(x)\)).

  Using the pair \((\mu, \lambda)\) obtained by the t'CycleFinder', this
  function computes

  \[ f^n(x) = \begin{cases}
       f^n(x)                                 & \text{if } n < \mu, \\
       f^{\mu + ((n - \mu) \bmod \lambda)}(x) & \text{if } n \ge \mu.
     \end{cases} \]

  which allows \(f^n(x)\) to be computed for very large \(n\) without requiring
  \(n\) function applications.

  Note that this function will use a lazy list generated by @iterate f x@. This
  list will only be evaluated up to \(\mu + \lambda\) elements and is shared
  between the cycle finding phase and the computation of the value after @n@
  iterations, but might still require a significant amount of memory. Use
  'cycleExp'' if you'd rather re-evaluate @f@ many more times but use less
  memory at the expense of more time.

  The lazy list might also be evaluated further than \(\mu + \lambda\)
  depending on the cycle finding algorithm chosen ('brent', 'floyd').

  >>> f x = x^42 `mod` 1000003 -- cycle (1, 83333)
  >>> g = cycleExp nivash f 23
  >>> g 0 -- after 0 iterations
  > 23
  >>> -- after a googol iterations, but finishes in less than the current
  >>> -- age of the universe
  >>> g (10^100)
  > 671872
-}
cycleExp :: CycleFinder a -> (a -> a) -> a -> Integer -> a
cycleExp alg f x = cycleExpWith alg listInput (iterate f x)

-- | Like 'cycleExp', but doesn't cache. Probably not very useful in practice.
cycleExp' :: CycleFinder a -> (a -> a) -> a -> Integer -> a
cycleExp' alg f = cycleExpWith alg (funcInput f)

data NaiveContainer m a = NaiveContainer
    { emptyC :: m
    , lookupC :: a -> m -> Maybe Int
    , insertC :: a -> Int -> m -> m
    }

{-# INLINE naive #-}
naive :: NaiveContainer m a -> Input s a -> s -> (Int, Int)
naive NaiveContainer{..} Input{..} = go 0 emptyC . inpUncons
  where
    go i _ Nothing = (i, 0)
    go i m (Just (x, xs))
        | Just j <- lookupC x m = (j, i - j)
        | otherwise = go (i + 1) (insertC x i m) (inpUncons xs)

{-# SPECIALIZE naiveOrd' :: (Ord a) => Input a a -> a -> (Int, Int) #-}
{-# SPECIALIZE naiveOrd' :: (Ord a) => Input [a] a -> [a] -> (Int, Int) #-}
naiveOrd' :: (Ord a) => Input s a -> s -> (Int, Int)
naiveOrd' = naive (NaiveContainer M.empty M.lookup M.insert)

-- | Naive cycle finding algorithm using t'Data.Map.Strict.Map'.
naiveOrd :: (Ord a) => CycleFinder a
naiveOrd = CycleFinder naiveOrd'

{-# SPECIALIZE naiveHashable' :: (Hashable a) => Input a a -> a -> (Int, Int) #-}
{-# SPECIALIZE naiveHashable' :: (Hashable a) => Input [a] a -> [a] -> (Int, Int) #-}
naiveHashable' :: (Hashable a) => Input s a -> s -> (Int, Int)
naiveHashable' = naive (NaiveContainer HM.empty HM.lookup HM.insert)

-- | Naive cycle finding algorithm using t'Data.HashMap.Strict.HashMap'.
naiveHashable :: (Hashable a) => CycleFinder a
naiveHashable = CycleFinder naiveHashable'

{-# INLINE brent' #-}
{-# SPECIALIZE brent' :: (Eq a) => Input a a -> a -> (Int, Int) #-}
{-# SPECIALIZE brent' :: (Eq a) => Input [a] a -> [a] -> (Int, Int) #-}
brent' :: (Eq a) => Input s a -> s -> (Int, Int)
brent' Input{..} = maybe (0, 0) (uncurry (findLambda 1 1)) . inpUncons
  where
    findLambda pow lambda t hs =
        maybe (pow + lambda - 1, 0) (uncurry go) (inpUncons hs)
      where
        go h hs'
            | t == h = (pow, lambda)
            | pow == lambda = findLambda (2 * pow) 1 h hs'
            | otherwise = findLambda pow (1 + lambda) t hs'

{- |
  Brent's cycle finding algorithm.

  Evaluates at most \(2(\mu + \lambda)\) elements of the sequence.

  Always better than floyd.

  * [Brent, R. P. "An improved Monte Carlo factorization algorithm", BIT Numerical Mathematics, 20(2):176–184, 1980.](https://maths-people.anu.edu.au/~brent/pd/rpb051i.pdf)
  * <https://en.wikipedia.org/wiki/Cycle_detection#Brent's_algorithm>
-}
brent :: (Eq a) => CycleFinder a
brent = CycleFinder brent'

{-# INLINE nivash' #-}
{-# SPECIALIZE nivash' :: (Ord a) => Input a a -> a -> (Int, Int) #-}
{-# SPECIALIZE nivash' :: (Ord a) => Input [a] a -> [a] -> (Int, Int) #-}
-- TODO: add a variant with stack partitioning, probably requiring a partitioning
--       function as an extra argument. this version can use (const 0).
nivash' :: (Ord a) => Input s a -> s -> (Int, Int)
nivash' Input{..} = go 0 []
  where
    go i stack = maybe (i, 0) (uncurry go') . inpUncons
      where
        go' x s
            | (sx, si) : _ <- stack', sx == x = (si, i - si)
            | otherwise = go (i + 1) ((x, i) : stack') s
          where
            stack' = dropWhile ((> x) . fst) stack

-- TODO: Gosper? maybe not really that useful in practice.

{- |
  Nivash's cycle finding algorithm.

  Never computes an element at a given position in the sequence more than once.

  Might use memory proportional to \(\mu + \lambda\) in the worst case of an
  ascending sequence, but commonly uses much less for reasonably "random"
  sequences.

  Can often be faster than 'brent' while not using nearly as much memory as
  'naiveOrd' or 'naiveHashable'.

  * [G. Nivasch, "Cycle detection using a stack", Information Processing Letters 90/3, pp. 135-140, 2004.](https://drive.google.com/file/d/16H_lrjeaBJqWvcn07C_w-6VNHldJ-ZZl/view)
-}
nivash :: (Ord a) => CycleFinder a
nivash = CycleFinder nivash'

-- TODO: Sedgewick, Szymanski, Yao

{-# INLINE floyd' #-}
{-# SPECIALIZE floyd' :: (Eq a) => Input a a -> a -> (Int, Int) #-}
{-# SPECIALIZE floyd' :: (Eq a) => Input [a] a -> [a] -> (Int, Int) #-}
floyd' :: (Eq a) => Input s a -> s -> (Int, Int)
floyd' Input{..} s = detectCycle 0 s s
  where
    detectCycle n ts hs =
        fromMaybe (2 * n, 0) $
            go <$> inpUncons ts <*> (inpUncons . snd =<< skipped)
                <|> (2 * n + 1, 0) <$ skipped
      where
        skipped = inpUncons hs
        go (t, ts') (h, hs')
            | t == h = (n, findLambda 1 t ts')
            | otherwise = detectCycle (n + 1) ts' hs'
    findLambda n m ms =
        maybe n (uncurry go) (inpUncons ms)
      where
        go x xs
            | m == x = n
            | otherwise = findLambda (n + 1) m xs

{- |
  Floyd's / Tortoise and Hare cycle finding algorithm.

  Always worse than 'brent'. Don't use this.

  * <https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_tortoise_and_hare>
-}
floyd :: (Eq a) => CycleFinder a
floyd = CycleFinder floyd'

{- |
  Compute a minimal result \((\mu, \lambda)\) from a partial result
  \((\tilde{\mu}, \lambda)\).

  This involves re-traversing the sequence from the start and from \(\lambda\)
  which might be expensive for large \(\mu\). This should largely be negligible
  if you're running the t'CycleFinder' using any of the functions which cache
  the sequence of values (any but 'findCycle' and 'cycleExp'').
-}
minimalMu :: (Eq a) => CycleFinder a -> CycleFinder a
minimalMu alg = CycleFinder go
  where
    go inp@Input{..} s = maybeFindMu (runCycleFinder alg inp s)
      where
        maybeFindMu r@(_, lambda)
            | lambda == 0 = r
            | otherwise = (findMu 0 s (inpAdvance lambda s), lambda)
        findMu mu ts ms =
            fromMaybe mu $ go' <$> inpUncons ts <*> inpUncons ms
          where
            go' (t, ts') (m, ms')
                | t == m = mu
                | otherwise = findMu (mu + 1) ts' ms'
