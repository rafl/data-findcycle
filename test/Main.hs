{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Applicative ((<*>))
import Data.FindCycle
import Data.Foldable (find)
import Data.Functor ((<$>))
import Data.Maybe
import Data.Numbers.Primes
import Test.Tasty
import Test.Tasty.QuickCheck
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

totalAlgs :: [(String, CycleFinder Integer)]
totalAlgs =
    [ ("naiveHashable", naiveHashable)
    , ("naiveOrd", naiveOrd)
    ]

partialAlgs :: [(String, CycleFinder Integer)]
partialAlgs =
    [ ("nivash", nivash)
    , ("brent", brent)
    , ("floyd", floyd)
    ]

defAlg :: CycleFinder Integer
defAlg = nivash

type Runner r = Cycle -> r
type Extractor = Runner (Int, Int, ([Integer], [Integer]))

defExtractor :: CycleFinder Integer -> Extractor
defExtractor alg Cycle{..} = findCycleExtract alg cycF cycX0

extractors :: [(String, CycleFinder Integer -> Extractor)]
extractors =
    [ ("findCycleExtract", defExtractor)
    ,
        ( "unsafeFindCycleFromList"
        , \alg Cycle{..} -> unsafeFindCycleFromList alg (iterate cycF cycX0)
        )
    ]

discardExtract :: Runner (a, a, b) -> Runner (a, a)
discardExtract f c = (mu, lambda)
  where
    (mu, lambda, _) = f c

prop_algCorrect :: CycleFinder Integer -> Cycle -> Property
prop_algCorrect alg Cycle{..} = findCycle alg cycF cycX0 === (cycMu, cycLambda)

prop_algsAgree :: CycleFinder Integer -> CycleFinder Integer -> Cycle -> Property
prop_algsAgree a b Cycle{..} =
    findCycleExtract a cycF cycX0 === findCycleExtract b cycF cycX0

prop_runnersAgree :: (Eq r, Show r) => Runner r -> Runner r -> Cycle -> Property
prop_runnersAgree a b c = a c === b c

prop_muUpperBound :: CycleFinder Integer -> Cycle -> Property
prop_muUpperBound alg Cycle{..} =
    counterexample ("Should be at least " ++ show cycMu) $
        fst (findCycle alg cycF cycX0) >= cycMu

prop_extract :: CycleFinder Integer -> Cycle -> Property
prop_extract alg Cycle{..} =
    (length pre, length cyc, pre ++ cyc ++ cyc)
        === (mu, lambda, take (mu + 2 * lambda) (iterate cycF cycX0))
  where
    (mu, lambda, (pre, cyc)) = findCycleExtract alg cycF cycX0

prop_cycleExp :: CycleFinder Integer -> Cycle -> Property
prop_cycleExp alg Cycle{..} =
    property $ \(NonNegative n) ->
        counterexample ("n=" ++ show n) $
            g (fromIntegral n)
                === xs !! (n - max 0 (n - cycMu - ((n - cycMu) `mod` cycLambda)))
  where
    g = cycleExp alg cycF cycX0
    xs = iterate cycF cycX0

prop_cycleExpsAgree :: CycleFinder Integer -> Cycle -> Property
prop_cycleExpsAgree alg Cycle{..} =
    property $ \(NonNegative (n :: Int)) ->
        counterexample ("n=" ++ show n) $
            g (fromIntegral n) === g' (fromIntegral n)
  where
    g = cycleExp alg cycF cycX0
    g' = cycleExp' alg cycF cycX0

prop_finite :: CycleFinder Integer -> Cycle -> Property
prop_finite alg Cycle{..} =
    unsafeFindCycleFromList (minimalMu alg) (take cycMu xs)
        === (cycMu, 0, (take cycMu xs, []))
  where
    xs = iterate cycF cycX0

tests :: TestTree
tests =
    testGroup
        "Data.FindCycle minimal tests"
        [ let (name, alg) : _ = totalAlgs
          in testProperty
                (name ++ " is correct")
                (prop_algCorrect alg)
        , testGroup
            "All total algorithms agree"
            [ testProperty (refName ++ " ~ " ++ name) (prop_algsAgree refAlg alg)
            | let ((refName, refAlg) : algs) = totalAlgs
            , (name, alg) <- algs
            ]
        , testGroup
            "Total agrees with minimalMu of partial"
            [ testProperty
                (refName ++ " ~ minimalMu " ++ algName)
                (prop_algsAgree refAlg (minimalMu alg))
            | let ((refName, refAlg) : _) = totalAlgs
            , (algName, alg) <- partialAlgs
            ]
        , testGroup
            "mu upper bound for partial"
            [ testProperty name (prop_muUpperBound alg)
            | (name, alg) <- partialAlgs
            ]
        , testProperty
            "minimalMu is idempotent"
            (prop_algsAgree (minimalMu defAlg) (minimalMu (minimalMu defAlg)))
        , testGroup
            "Extractors agree"
            [ testProperty
                (refName ++ " ~ " ++ rName)
                (prop_runnersAgree (refR defAlg) (r defAlg))
            | let ((refName, refR) : rs) = extractors
            , (rName, r) <- rs
            ]
        , testProperty
            "findCycle agrees with extractors"
            ( prop_runnersAgree
                (discardExtract (defExtractor defAlg))
                (\Cycle{..} -> findCycle defAlg cycF cycX0)
            )
        , testProperty "extraction is correct" (prop_extract defAlg)
        , testProperty "cycleExp matches naive iteration" (prop_cycleExp defAlg)
        , testProperty "cycleExp' agrees with cycleExp " (prop_cycleExpsAgree defAlg)
        , testGroup
            "finite lists"
            [ testProperty name (prop_finite alg)
            | (name, alg) <- totalAlgs ++ partialAlgs
            ]
        ]

main :: IO ()
main = defaultMain tests
