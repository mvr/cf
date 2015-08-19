{-# LANGUAGE FlexibleInstances #-}
module Math.ContinuedFraction.Interval where

import Data.Ratio
import Numeric

data Extended a = Finite a | Infinity deriving (Eq)

data Interval a = Interval (Extended a) (Extended a) Bool deriving (Eq)

instance Show (Interval Rational) where
  show (Interval a b _) = "(" ++ showE a ++ ", " ++ showE b ++ ")"
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

instance (Show a) => Show (Extended a) where
  show (Finite r) = show r
  show Infinity = "Infinity"

interval :: Ord a => Extended a -> Extended a -> Interval a
interval (Finite i) (Finite s) = Interval (Finite i) (Finite s) (i <= s)
interval i s = Interval i s True
{-# INLINE interval #-}

smallerThan :: (Num a, Ord a) => Interval a -> Interval a -> Bool
Interval _ _ _ `smallerThan` Interval Infinity Infinity _ = False -- TODO CHECK
Interval Infinity Infinity _ `smallerThan` Interval _ _ _ = True
Interval (Finite a) Infinity _ `smallerThan` Interval (Finite b) Infinity _ = a >= b
Interval (Finite a) Infinity _ `smallerThan` Interval Infinity (Finite b) _ = a >= -b
Interval Infinity (Finite a) _ `smallerThan` Interval (Finite b) Infinity _ = a <= -b
Interval Infinity (Finite a) _ `smallerThan` Interval Infinity (Finite b) _ = a <= b
Interval (Finite i1) (Finite s1) _ `smallerThan` Interval Infinity (Finite _) _ = i1 <= s1
Interval (Finite i1) (Finite s1) _ `smallerThan` Interval (Finite _) Infinity _ = i1 <= s1
Interval Infinity (Finite _) _ `smallerThan` Interval (Finite i2) (Finite s2) False = True
Interval (Finite _) Infinity _ `smallerThan` Interval (Finite i2) (Finite s2) False = True
Interval Infinity (Finite _) _ `smallerThan` Interval (Finite i2) (Finite s2) True = False
Interval (Finite _) Infinity _ `smallerThan` Interval (Finite i2) (Finite s2) True = False
Interval (Finite i1) (Finite s1) True `smallerThan` Interval (Finite i2) (Finite s2) True
  = s1 - i1 <= s2 - i2
Interval (Finite i1) (Finite s1) False `smallerThan` Interval (Finite i2) (Finite s2) False
  = i1 - s1 >= i2 - s2
Interval (Finite i1) (Finite s1) True `smallerThan` Interval (Finite i2) (Finite s2) False
  = True
Interval (Finite i1) (Finite s1) False `smallerThan` Interval (Finite i2) (Finite s2) True
  = False

epsilon :: Rational
epsilon = 1 % 10^10

comparePosition :: Interval Rational -> Interval Rational -> Maybe Ordering
Interval (Finite i1) (Finite s1) True `comparePosition` Interval (Finite i2) (Finite s2) True
  | s1 < i2 = Just LT
  | s2 < i1 = Just GT
  | (s1 - i1) < epsilon && (s2 - i2) < epsilon = Just EQ
_ `comparePosition` _ = Nothing

intervalDigit :: (RealFrac a) => Interval a -> Maybe Integer
intervalDigit (Interval (Finite i) (Finite s) True) =
  if floor i == floor s && floor i >= 0 then
    Just $ floor i
  else
    Nothing
intervalDigit _ = Nothing

subset :: Ord a => Interval a -> Interval a -> Bool
Interval _ _ _ `subset` Interval Infinity Infinity _ = True
Interval Infinity Infinity _ `subset` Interval _ _ _ = False
Interval Infinity (Finite s1) _ `subset` Interval Infinity (Finite s2) _ = s1 <= s2
Interval (Finite i1) Infinity _ `subset` Interval (Finite i2) Infinity _ = i1 >= i2
Interval Infinity (Finite _) _ `subset` Interval (Finite _) Infinity _ = False
Interval (Finite _) Infinity _ `subset` Interval Infinity (Finite _) _ = False
Interval (Finite i1) (Finite s1) True `subset` Interval Infinity (Finite s2) _
  | s1 <= s2  = True
  | otherwise = False
Interval (Finite i1) (Finite s1) False `subset` Interval Infinity (Finite s2) _
  = False
Interval (Finite i1) (Finite s1) True `subset` Interval (Finite i2) Infinity _
  | i2 <= i1  = True
  | otherwise = False
Interval (Finite i1) (Finite s1) False `subset` Interval (Finite i2) Infinity _
  = False
Interval Infinity (Finite s1) _ `subset` Interval (Finite i2) (Finite s2) False
  | s1 <= s2  = True
  | otherwise = False
Interval Infinity (Finite s1) _ `subset` Interval (Finite i2) (Finite s2) True
  = False
Interval (Finite i1) Infinity _ `subset` Interval (Finite i2) (Finite s2) False
  | i2 <= i1  = True
  | otherwise = False
Interval (Finite i1) Infinity _ `subset` Interval (Finite i2) (Finite s2) True
  = False
Interval (Finite i1) (Finite s1) True `subset` Interval (Finite i2) (Finite s2) True
  | i2 <= i1 && s1 <= s2 = True
  | otherwise            = False
Interval (Finite i1) (Finite s1) False `subset` Interval (Finite i2) (Finite s2) False
  | i2 <= i1 && s1 <= s2 = True
  | otherwise            = False
Interval (Finite i1) (Finite s1) True `subset` Interval (Finite i2) (Finite s2) False
  | i2 <= i1 && i2 <= s1 = True
  | i1 <= s2 && s1 <= s2 = True
  | otherwise            = False
Interval (Finite i1) (Finite s1) False `subset` Interval (Finite i2) (Finite s2) True
  = False

elementOf :: (Ord a) => Extended a -> Interval a -> Bool
Infinity `elementOf` (Interval Infinity Infinity _) = True
(Finite _) `elementOf` (Interval Infinity Infinity _) = True
Infinity `elementOf` (Interval (Finite _) Infinity _) = True
(Finite x) `elementOf` (Interval (Finite a) Infinity _) = x >= a
Infinity `elementOf` (Interval Infinity (Finite _) _) = True
(Finite x) `elementOf` (Interval Infinity (Finite b) _) = x <= b
Infinity `elementOf` (Interval (Finite i) (Finite s) _) = i > s
(Finite x) `elementOf` (Interval (Finite i) (Finite s) True) = i <= x && x <= s
(Finite x) `elementOf` (Interval (Finite i) (Finite s) False) = i <= x || x <= s

-- Here we interpret Interval Infinity Infinity as the whole real line
mergeInterval :: (Ord a) => Interval a -> Interval a -> Interval a
mergeInterval (Interval Infinity Infinity _) (Interval Infinity Infinity _)
  = Interval Infinity Infinity True
mergeInterval (Interval (Finite i) Infinity _) (Interval Infinity Infinity _)
  = Interval Infinity Infinity True
mergeInterval (Interval Infinity (Finite s) _) (Interval Infinity Infinity _)
  = Interval Infinity Infinity True
mergeInterval (Interval (Finite i) (Finite s) _) (Interval Infinity Infinity _)
  = Interval Infinity Infinity True
mergeInterval (Interval Infinity (Finite s) _) (Interval (Finite i) Infinity _)
  | s >= i    = Interval Infinity Infinity True
  | otherwise = Interval (Finite i) (Finite s) False
mergeInterval (Interval Infinity (Finite s1) _) (Interval Infinity (Finite s2) _)
  = Interval Infinity (Finite $ max s1 s2) True
mergeInterval (Interval (Finite i1) Infinity _) (Interval (Finite i2) Infinity _)
  = Interval Infinity (Finite $ min i1 i2) True
mergeInterval (Interval (Finite i1) (Finite s1) True) (Interval (Finite i2) Infinity _)
  = Interval (Finite $ min i1 i2) Infinity True
mergeInterval (Interval (Finite i1) (Finite s1) False) (Interval (Finite i2) Infinity _)
  | i1 <= i2 = Interval (Finite i1) (Finite s1) False
  | i2 <= s1 = Interval Infinity Infinity True
  | i2 >  s1 = Interval (Finite i2) (Finite s1) False
mergeInterval (Interval (Finite i1) (Finite s1) True) (Interval Infinity (Finite s2) _)
  = Interval Infinity (Finite $ max s1 s2) True
mergeInterval (Interval (Finite i1) (Finite s1) False) (Interval Infinity (Finite s2) _)
  | s2 <= s1 = Interval (Finite i1) (Finite s1) False
  | i1 <= s2 = Interval Infinity Infinity True
  | i1 >  s2 = Interval (Finite i1) (Finite s2) False
mergeInterval (Interval (Finite i1) (Finite s1) True) (Interval (Finite i2) (Finite s2) True)
  = Interval (Finite $ min i1 i2) (Finite $ max s1 s2) True
mergeInterval (Interval (Finite i1) (Finite s1) False) (Interval (Finite i2) (Finite s2) False)
  | (i1 <= s2 || i2 <= s1) = Interval Infinity Infinity True
  | otherwise              = Interval (Finite $ min i1 i2) (Finite $ max s1 s2) False
mergeInterval int1@(Interval (Finite i1) (Finite s1) True) int2@(Interval (Finite i2) (Finite s2) False)
  = doTricky int1 int2
mergeInterval int1@(Interval (Finite i1) (Finite s1) False) int2@(Interval (Finite i2) (Finite s2) True)
  = doTricky int2 int1
mergeInterval int1 int2 = mergeInterval int2 int1

doTricky int1@(Interval (Finite i1) (Finite s1) True) int2@(Interval (Finite i2) (Finite s2) False)
          | int1 `subset` int2         = int2
          | i2 <= s1 && i1 <= s2       = Interval Infinity Infinity True
          | s1 < i2  = Interval (Finite i2) (Finite s1) False
          | s2 < i1  = Interval (Finite i1) (Finite s2) False
          | otherwise = error "The impossible happened in mergeInterval"
