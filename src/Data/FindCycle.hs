{-|
Module: Data.FindCycle
Description: Find cycles in periodic functions (and lists)
Copyright: (c) 2024 Florian Ragwitz
License: MIT

Any function @f :: a -> a@ where the type @a@ has finitely many elements
eventually has to be cyclic when iterated from some initial @a@.

This module provides a number of common algorithms to detect and identify such
cycles.

For typical usage, you probably want to use either

@
let (mu', lambda) = findCycle brent f x
@

for finding cycles using a constant amount of memory, or

@
let (mu', lambda) = findCycle nivash f x
@

to use a logarithmic amount of memory while finding the result faster if @f@ is
fairly randomly distributed.

If you care about the non-cyclic prefix length being minimal, the above
examples become:

@
let (mu, lambda) = findCycle (minimalMu brent) f x
let (mu, lambda) = findCycle (minimalMu nivash) f x
@

-}

module Data.FindCycle
  (
  -- * CycleFinder type
  CycleFinder
  -- * Algorithms
  {-|
       These base algorithms all return a pair of integers
       \((\tilde{\mu}, \lambda)\), where \(\tilde{\mu}\) represents an upper
       bound for the length of the non-cyclic prefix of the sequence, and
       \(\lambda\) represents the length of the cycle.

       They return a non-minimal \(\tilde{\mu}\) only, because for many
       practical applications it's perfectly sufficient and cheaper to comptute.
       For example ....

       If a minimal \(\mu\) is needed, 'minimalMu' can be used to transform
       these 'CycleFinder's into ones returning \((\mu, \lambda)\).

       The \(\lambda\) returned is always minimal and never a multiple of the
       true cycle length.
  -}
  , brent
  , floyd
  , nivash
  -- * Running algorithms
  , findCycle
  , unsafeFromList
  -- * Modifiers
  , minimalMu
  , extract
  , cached
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

{-|
An algorithm to find cycles in a function from @a@ to @a@.
@r@ represents the type of the result returned by the algorithm.
-}
newtype CycleFinder a r = CycleFinder { runCycleFinder :: Input a -> r }

-- | Implements Brent's cycle finding algorithm.
brent :: (Eq a) => CycleFinder a (Int, Int)
brent = CycleFinder $ \s ->
  maybe (0, 0) (uncurry (findLambda 1 1)) (inpUncons s)
  where findLambda pow lambda t hs =
          maybe (pow+lambda-1, 0) (uncurry go) (inpUncons hs)
          where go h hs'
                  | t == h = (pow, lambda)
                  | pow == lambda = findLambda (2*pow) 1 h hs'
                  | otherwise = findLambda pow (1+lambda) t hs'

-- | Implements Nivash's cycle finding algorithm.
nivash :: (Ord a) => CycleFinder a (Int, Int)
nivash = CycleFinder $ go 0 []
  where go i stack st = maybe (i, 0) (uncurry go') (inpUncons st)
          where go' x st'
                  | (sx, si) : _ <- stack', sx == x = (si, i - si)
                  | otherwise = go (i + 1) ((x, i):stack') st'
                  where stack' = dropWhile ((> x) . fst) stack

-- | Implements the Floyd / Tortoise and Hare cycle finding algorithm.
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

-- | Runs the 'CycleFinder' for the given function and starting value.
findCycle :: CycleFinder a r -> (a -> a) -> a -> r
findCycle alg f x = runCycleFinder alg (FuncInput f x)

{-|
Runs the 'CycleFinder' for a given input list.

This function is provided as a convenience for when you already have a list of
values you'd like to find cycles in. It's referred to as "unsafe", because it
might lead to surprising results when the input doesn't satisfy the invariants
that different algorithms assume.

All algorithms assume that the sequence they're searching can be constructed by
repeated function application from a starting value. Many sequences can't, such
as @[1,2,1,3,1,4,1,5,...]@ (because there can only be one unique successor of
@1@).

Algorithms also assume the input sequence to be infinite, and they will
commonly consume more than \(\mu + \lambda\) (or \(\tilde{\mu} + \lambda\))
elements from it. If you provide a finite input list, cycles might not be
identified correctly if the chosen algorithm runs into the end of it, even
though the input does technically contain an identifiable cycle.

If an assumption is violated, algorithms might wrongly identify cycles or never
terminate. Try to stick to 'findCycle' if possible, or only pass infinite lists
generated via @iterate f x@ (or equivalent) to 'unsafeFromList'.

-}
unsafeFromList :: CycleFinder a r -> [a] -> r
unsafeFromList alg = runCycleFinder alg . ListInput

{-|
Compute a minimal result \((\mu, \lambda)\) from a partial
result \((\tilde{\mu}, \lambda)\).
-}
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

{-|
Transform a 'CycleFinder' returning \((a, b)\) into one returning a pair of
lists \((ps, cs)\) where \(ps\) contains the first \(a\) from the beginning of
the sequence, and \(cs\) contains \(b\) elements of the sequence after
skipping \(a\) elements.

If \((a, b)\) is the result of 'minimalMu' of one of the algorithms run
against @f@ and @x@, then @iterate f x == ps ++ cycle cs@.

If you're extracting these lists anyway, you likely want to combine
'extract' with 'cached' to avoid unnecessary recomputations, as you're paying
the penalty in memory usage already.
-}
extract :: (Eq a) => CycleFinder a (Int, Int) -> CycleFinder a ([a],[a])
extract alg = CycleFinder $ \s -> extractList s (runCycleFinder alg s)
  where extractList s (mu, lambda) = take lambda <$> splitAt mu (gatherAll s)
        gatherAll (ListInput xs) = xs
        gatherAll (FuncInput f x) = iterate f x

{-|
Transform a 'CycleFinder' from one which will always call the function it's
operating on to get a given element in the sequence, to one which caches those
function calls in an infinite list available for reuse if the algorithm chosen
revisits the same element more than once.

The entire sequence up to whichever point the algorithm traversed it to will be
kept in memory, effectively negating the desirable properties of constant or
logarithmic memory usage of the algorithms. Also, a more naive cycle finding
algorithm would probably be more efficient than anything currently provided in
this library if you're keeping each function result in memory anyway. (Such a
naive algorithm might be provided in the future).

Note that 'cached' needs to be used on the very outside of a 'CycleFinder', e.g.
@cached (extract (minimalMu brent))@, or it will have no effect that functions
like 'minimalMu' or 'extract' can benefit from, and only consumes extra memory.
-}
cached :: CycleFinder a r -> CycleFinder a r
cached (CycleFinder alg) = CycleFinder cache
  where cache s@(ListInput _) = alg s
        cache (FuncInput f x) = alg (ListInput (iterate f x))
