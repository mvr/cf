{-# LANGUAGE FlexibleInstances #-}
module Math.ContinuedFraction.Interval where

import Data.Ratio
import Numeric

data Extended a = Finite a | Infinity deriving (Eq)

data Interval a = Interval (Extended a) (Extended a) deriving (Eq)

instance Show (Interval Rational) where
  show (Interval a b) = "(" ++ showE a ++ ", " ++ showE b ++ ")"
    where showE Infinity = "Infinity"
          showE (Finite r) = show (fromRat r)

instance Num a => Num (Extended a) where
  Finite a + Finite b = Finite (a + b)
  Infinity + Finite _ = Infinity
  Finite _ + Infinity = Infinity
  Infinity + Infinity = error "Infinity + Infinity"

  Finite a * Finite b = Finite (a * b)
  Infinity * Finite a = Infinity
  -- Infinity * Finite a | a == 0 = error "Infinity * 0"
  --                     | otherwise = Infinity
  Finite a * i = i * Finite a
  Infinity * Infinity = undefined "Infinity * Infinity"

  negate (Finite r) = Finite (-r)
  negate Infinity = Infinity

  signum (Finite r) = Finite $ signum r
  signum Infinity = error "signum Infinity"

  abs (Finite r) = Finite $ abs r
  abs Infinity = Infinity

  fromInteger = Finite . fromInteger

-- Hack!
instance (Ord a) => Ord (Extended a) where
  Finite a <= Finite b = a <= b
  Infinity <= Finite _ = True
  Finite _ <= Infinity = True
  Infinity <= Infinity = True

  max (Finite a) (Finite b) = Finite (max a b)
  max _ _ = Infinity

  min (Finite a) (Finite b) = Finite (min a b)
  min _ _ = Infinity

instance (Show a) => Show (Extended a) where
  show (Finite r) = show r
  show Infinity = "Infinity"

instance (Num a, Ord a) => Ord (Interval a) where
  Interval _ _ <= Interval Infinity Infinity = True
  Interval Infinity Infinity <= Interval _ _ = False
  Interval i1 s1 <= Interval i2 s2 =    (i1 <= s1 && i2 <= s2 && s1 - i1 <= s2 - i2)
                                     || (i1 >  s1 && i2 >  s2 && i1 - s1 >= i2 - s2)
                                     || (i1 <= s1 && i2 >  s2)


epsilon :: Rational
epsilon = 1 % 10^10

comparePosition :: Interval Rational -> Interval Rational -> Maybe Ordering
Interval (Finite i1) (Finite s1) `comparePosition` Interval (Finite i2) (Finite s2)
  | i1 > s1 = Nothing
  | i2 > s2 = Nothing
  | s1 < i2 = Just LT
  | s2 < i1 = Just GT
  | (s1 - i1) < epsilon && (s2 - i2) < epsilon = Just EQ
_ `comparePosition` _ = Nothing

intervalDigit :: (RealFrac a) => Interval a -> Maybe Integer
intervalDigit (Interval (Finite i) (Finite s)) = if i <= s && floor i == floor s && floor i >= 0 then
                                                   Just $ floor i
                                                 else
                                                   Nothing
intervalDigit _ = Nothing

subset :: Ord a => Interval a -> Interval a -> Bool
Interval _ _ `subset` Interval Infinity Infinity = True
Interval Infinity Infinity `subset` Interval _ _ = False
Interval Infinity (Finite s1) `subset` Interval Infinity (Finite s2) = s1 <= s2
Interval (Finite i1) Infinity `subset` Interval (Finite i2) Infinity = i1 >= i2
Interval Infinity (Finite _) `subset` Interval (Finite _) Infinity = False
Interval (Finite _) Infinity `subset` Interval Infinity (Finite _) = False
Interval (Finite i1) (Finite s1) `subset` Interval Infinity (Finite s2)
  | i1 <= s1 && s1 <= s2 = True
  | otherwise            = False
Interval (Finite i1) (Finite s1) `subset` Interval (Finite i2) Infinity
  | i1 <= s1 && i2 <= i1 = True
  | otherwise            = False
Interval Infinity (Finite s1) `subset` Interval (Finite i2) (Finite s2)
  | i2 > s2 && s1 <= s2 = True
  | otherwise            = False
Interval (Finite i1) Infinity `subset` Interval (Finite i2) (Finite s2)
  | i2 > s2 && i2 <= i1 = True
  | otherwise            = False
Interval (Finite i1) (Finite s1) `subset` Interval (Finite i2) (Finite s2)
  | i1 <= s1 && i2 <= s2 &&
    i2 <= i1 && s1 <= s2     = True
  | s1 <  i1 && s2 <  i2 &&
    i2 <= i1 && s1 <= s2     = True
  | i1 <= s1 && s2 <  i2 &&
    i2 <= i1 && i2 <= s1     = True
  | i1 <= s1 && s2 <  i2 &&
    i1 <= s2 && s1 <= s2     = True
  | otherwise                = False

elementOf :: (Ord a) => Extended a -> Interval a -> Bool
x `elementOf` (Interval i s) | i <= s = i <= x && x <= s
                             | i >= s = i <= x || x <= s
                             | otherwise = error "The impossible happened in elementOf"

mergeInterval :: (Ord a) => Interval a -> Interval a -> Interval a
mergeInterval int1@(Interval i1 s1) int2@(Interval i2 s2) | i1 <= s1 && i2 <= s2 = Interval (min i1 i2) (max s1 s2)
                                                          | i1 >= s1 && i2 >= s2 && (i1 <= s2 || i2 <= s1) = Interval Infinity Infinity
                                                          | i1 >= s1 && i2 >= s2 = Interval (min i1 i2) (max s1 s2)
                                                          | i1 >= s1 && i2 <= s2 = mergeInterval int2 int1
                                                          | i1 <= s1 && i2 >= s2 = doTricky
                                                          | otherwise = error "The impossible happened in mergeInterval"
  where doTricky | int1 `subset` int2         = int2
                 | i2 <= s1 && i1 <= s2       = Interval Infinity Infinity
                 | s1 /= Infinity && s1 < i2  = Interval i2 s1
                 | s1 == Infinity             = Interval i1 s2
                 | i1 /= Infinity && s2 < i1  = Interval i1 s2
                 | i1 == Infinity             = Interval i2 s1
                 | otherwise = error "The impossible happened in mergeInterval"
