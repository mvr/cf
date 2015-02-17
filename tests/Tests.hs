{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Maybe

import Math.ContinuedFraction.Effective
import Math.ContinuedFraction.Interval

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2

instance Arbitrary Extended where
  arbitrary = do
    b <- arbitrary :: Gen Bool
    if b then
      return Infinity
    else
      fmap Finite arbitrary

instance Arbitrary Interval where
  arbitrary = do
    (i, s) <- suchThat arbitrary (\(i,s) -> i /= s) :: Gen (Extended, Extended)
    return $ Interval i s

prop_sensibleEmittable x = isJust $ existsEmittable (primitiveBound x)
  where types = x :: Integer

prop_sensiblePrimitiveBound x = fromInteger x `elementOf` primitiveBound x
  where types = x :: Integer

prop_sensibleMergeInterval a b = a `subset` ab && b `subset` ab
  where types = (a :: Interval, b :: Interval)
        ab = a `mergeInterval` b

main :: IO ()
main = $defaultMainGenerator
