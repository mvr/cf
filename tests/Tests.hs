{-# LANGUAGE TemplateHaskell #-}
module Main where

import Math.ContinuedFraction.Effective

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2

main :: IO ()
main = $defaultMainGenerator
