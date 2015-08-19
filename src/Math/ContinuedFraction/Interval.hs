{-# LANGUAGE FlexibleInstances #-}
module Math.ContinuedFraction.Interval where

import Data.Ratio

data Extended a = Finite a | Infinity deriving (Eq)

data Interval a = Everything
                | Empty
                | LeftInfinite a
                | RightInfinite a
                | Inside a a
                | Outside a a deriving (Eq)

instance Show a => Show (Interval a) where
  show Everything = "(Inf, Inf)"
  show Empty = "(,)"
  show (LeftInfinite a) = "(Inf, " ++ show a ++ ")"
  show (RightInfinite a) = "(" ++ show a ++ ", Inf)"
  show (Inside a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (Outside a b) = ")" ++ show a ++ ", " ++ show b ++ "("

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

interval :: (Ord a) => Extended a -> Extended a -> Interval a
interval Infinity Infinity = Everything
interval Infinity (Finite a) = LeftInfinite a
interval (Finite a) Infinity = RightInfinite a
interval (Finite a) (Finite b) | a <= b    = Inside a b
                               | otherwise = Outside b a
{-# INLINE interval #-}

leftStart :: Interval a -> Extended a
leftStart Everything = Infinity
leftStart (LeftInfinite _) = Infinity
leftStart (RightInfinite s) = Finite s
leftStart (Inside i _) = Finite i
leftStart (Outside _ s) = Finite s
{-# INLINE leftStart #-}

rightStart :: Interval a -> Extended a
rightStart Everything = Infinity
rightStart (LeftInfinite i) = Finite i
rightStart (RightInfinite _) = Infinity
rightStart (Inside _ s) = Finite s
rightStart (Outside i _) = Finite i
{-# INLINE rightStart #-}

smallerThan :: (Num a, Ord a) => Interval a -> Interval a -> Bool
_               `smallerThan` Everything      = True
Everything      `smallerThan` _               = False
Empty           `smallerThan` _               = True
_               `smallerThan` Empty           = False

Inside _ _      `smallerThan` LeftInfinite _  = True
LeftInfinite _  `smallerThan` Inside _ _      = False
Inside _ _      `smallerThan` RightInfinite _ = True
RightInfinite _ `smallerThan` Inside _ _      = False

Outside _ _     `smallerThan` LeftInfinite _  = False
Outside _ _     `smallerThan` RightInfinite _ = False
LeftInfinite _  `smallerThan` Outside _ _     = True
RightInfinite _ `smallerThan` Outside _ _     = True

LeftInfinite a  `smallerThan` LeftInfinite b  = a <= b
RightInfinite a `smallerThan` LeftInfinite b  = a >= -b
LeftInfinite a  `smallerThan` RightInfinite b = a <= -b
RightInfinite a `smallerThan` RightInfinite b = a >= b

Inside _ _      `smallerThan` Outside _ _     = True
Outside _ _     `smallerThan` Inside _ _      = False

Inside i1 s1    `smallerThan` Inside i2 s2    = s1 - i1 <= s2 - i2
Outside i1 s1   `smallerThan` Outside i2 s2   = s1 - i1 >= s2 - i2

epsilon :: Rational
epsilon = 1 % 10^10

comparePosition :: Interval Rational -> Interval Rational -> Maybe Ordering
Inside i1 s1 `comparePosition` Inside i2 s2
  | s1 < i2 = Just LT
  | s2 < i1 = Just GT
  | (s1 - i1) < epsilon && (s2 - i2) < epsilon = Just EQ
_ `comparePosition` _ = Nothing

intervalDigit :: (RealFrac a) => Interval a -> Maybe Integer
intervalDigit (Inside i s) = if floor i == floor s && floor i >= 0 then
                               Just $ floor i
                             else
                               Nothing
intervalDigit _ = Nothing

subset :: Ord a => Interval a -> Interval a -> Bool
_                `subset` Everything       = True
Everything       `subset` _                = False
Empty            `subset` _                = True
_                `subset` Empty            = False

LeftInfinite s1  `subset` LeftInfinite s2  = s1 <= s2
RightInfinite i1 `subset` RightInfinite i2 = i1 >= i2
LeftInfinite _   `subset` RightInfinite _  = False
RightInfinite _  `subset` LeftInfinite _   = False

Inside _ s1      `subset` LeftInfinite s2  = s1 <= s2
Inside i1 _      `subset` RightInfinite i2 = i1 >= i2
LeftInfinite _   `subset` Inside _ _       = False
RightInfinite _  `subset` Inside _ _       = False

Outside _ _      `subset` LeftInfinite _   = False
Outside _ _      `subset` RightInfinite _  = False
LeftInfinite s1  `subset` Outside i2 _     = s1 <= i2
RightInfinite i1 `subset` Outside _ s2     = i1 >= s2

Inside i1 s1     `subset` Inside i2 s2     = i2 <= i1 && s1 <= s2
Outside i1 s1    `subset` Outside i2 s2    = i1 <= i2 && s2 <= s1
Inside i1 s1     `subset` Outside i2 s2    = s1 <= i2 || i1 >= s2
Outside _ _      `subset` Inside _ _       = False

elementOf :: (Ord a) => Extended a -> Interval a -> Bool
_          `elementOf` Everything      = True
_          `elementOf` Empty           = False

Infinity   `elementOf` RightInfinite _ = True
Infinity   `elementOf` LeftInfinite _  = True
Infinity   `elementOf` Outside _ _     = True
Infinity   `elementOf` Inside _ _      = False

(Finite x) `elementOf` RightInfinite a = x >= a
(Finite x) `elementOf` LeftInfinite b  = x <= b
(Finite x) `elementOf` Inside i s      = i <= x && x <= s
(Finite x) `elementOf` Outside i s     = x <= i || s <= x

mergeInterval :: (Ord a) => Interval a -> Interval a -> Interval a
mergeInterval Everything _ = Everything
mergeInterval _ Everything = Everything
mergeInterval i Empty = i
mergeInterval Empty i = i

mergeInterval (LeftInfinite s) (RightInfinite i)
  | s >= i = Everything
  | otherwise = Outside s i
mergeInterval (RightInfinite i) (LeftInfinite s)
  | s >= i = Everything
  | otherwise = Outside s i
mergeInterval (LeftInfinite s1) (LeftInfinite s2)
  = LeftInfinite $ max s1 s2
mergeInterval (RightInfinite s1) (RightInfinite s2)
  = RightInfinite $ min s1 s2

mergeInterval (Inside i1 _) (RightInfinite i2)
  = RightInfinite $ min i1 i2
mergeInterval (RightInfinite i2) (Inside i1 _)
  = RightInfinite $ min i1 i2
mergeInterval (Outside i1 s1) (RightInfinite i2)
  | i2 >= s1 = Outside i1 s1
  | i2 <= i1 = Everything
  | otherwise = Outside i1 i2
mergeInterval y@(RightInfinite _) x@(Outside _ _)
  = mergeInterval x y

mergeInterval (Inside _ s1) (LeftInfinite s2)
  = RightInfinite $ max s1 s2
mergeInterval (LeftInfinite s2) (Inside _ s1)
  = RightInfinite $ max s1 s2
mergeInterval (Outside i1 s1) (LeftInfinite s2)
  | s2 <= i1 = Outside i1 s1
  | s2 >= s1 = Everything
  | otherwise = Outside s2 s1
mergeInterval y@(LeftInfinite _) x@(Outside _ _)
  = mergeInterval x y

mergeInterval (Inside i1 s1) (Inside i2 s2)
  = Inside (min i1 i2) (max s1 s2)
mergeInterval (Outside i1 s1) (Outside i2 s2)
  | i2 >= s1 || s2 <= i1 = Everything
  | otherwise = Outside (max i1 i2) (min s1 s2)

mergeInterval (Inside i1 s1) (Outside i2 s2)
  | i1 >= s2 = Outside i2 s2
  | s1 <= i2 = Outside i2 s2
  | i1 <= i2 && s1 >= s2 = Everything
  | s1 < i2 = Outside s1 s2
  | otherwise = Outside i2 i1
mergeInterval y@(Outside _ _) x@(Inside _ _)
  = mergeInterval x y
