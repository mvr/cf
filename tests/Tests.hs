{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Maybe

import Math.ContinuedFraction.Effective
import Math.ContinuedFraction.Interval

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2

prop_sensibleEmittable x = isJust $ existsEmittable (primitiveBound x)
  where types = x :: Integer

prop_sensiblePrimitiveBound x = fromInteger x `elementOf` primitiveBound x
  where types = x :: Integer

main :: IO ()
main = $defaultMainGenerator
