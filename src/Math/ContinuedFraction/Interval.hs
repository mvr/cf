module Math.ContinuedFraction.Interval where

import Data.Ratio

data Extended = Finite Rational | Infinity deriving (Eq)

data Interval = Interval Extended Extended deriving (Show, Eq)

instance Num Extended where
  Finite a + Finite b = Finite (a + b)
  Infinity + Finite _ = Infinity
  Finite _ + Infinity = Infinity
  Infinity + Infinity = undefined

  Finite a * Finite b = Finite (a * b)
  Infinity * Finite a | a == 0 = undefined
                      | otherwise = Infinity
  Finite a * i = i * Finite a

  negate (Finite r) = Finite (-r)
  negate Infinity = Infinity

  signum (Finite r) = Finite $ signum r
  signum Infinity = undefined

  abs (Finite r) = Finite $ abs r
  abs Infinity = Infinity

  fromInteger = Finite . fromInteger

instance Fractional Extended where
  recip (Finite 0) = Infinity
  recip (Finite r) = Finite (Prelude.recip r)
  recip Infinity = Finite 0

  fromRational = Finite

instance Real Extended where
  toRational (Finite r) = r
  toRational Infinity = undefined

instance RealFrac Extended where
  properFraction (Finite r) = (i, Finite q)
    where (i, q) = properFraction r
  properFraction Infinity = undefined

instance Ord Extended where
  Finite a <= Finite b = a <= b
  Infinity <= Finite _ = True
  Finite _ <= Infinity = True
  Infinity <= Infinity = True

  max (Finite a) (Finite b) = Finite (max a b)
  max _ _ = Infinity

  min (Finite a) (Finite b) = Finite (min a b)
  min _ _ = Infinity

instance Show Extended where
  show (Finite r) = show r
  show Infinity = "Infinity"

class Scalable s where
  (.+) :: Integer -> s -> s
  recips :: s -> s
  negates :: s -> s

instance Scalable Extended where
  q .+ (Finite r) = Finite (fromInteger q + r)
  _ .+ Infinity = Infinity

  recips = recip
  negates = negates

instance Scalable Interval where
  q .+ Interval i s = Interval (q .+ i) (q .+ s)
  recips (Interval i s) = Interval (recip s) (recip i)
  negates (Interval i s) = Interval (negate s) (negate i)

instance Ord Interval where
  Interval i1 s1 <= Interval i2 s2 =    (i1 <= s1 && i2 <= s2 && s1 - i1 <= s2 - i2)
                                     || (i1 >  s1 && i2 >  s2 && i1 - s1 >= i2 - s2)
                                     || (i1 <= s1 && i2 >  s2)

intervalDigit :: Interval -> Maybe Integer
intervalDigit (Interval (Finite i) (Finite s)) = if i <= s && floor i == floor s && floor i >= 0 then
                                                   Just $ floor i
                                                 else
                                                   Nothing
intervalDigit _ = Nothing

subset :: Interval -> Interval -> Bool
Interval i1 s1 `subset` Interval i2 s2 | i1 <= s1 && i2 <= s2 &&
                                         i2 <= i1 && s1 <= s2     = True
                                       | s1 <= i1 && s2 <= i2 &&
                                         i2 <= i1 && s1 <= s2     = True
                                       | i1 <= s1 && s2 <= i2 &&
                                         i2 <= i1 && i2 <= s1     = True
                                       | i1 <= s1 && s2 <= i2 &&
                                         i1 <= s2 && s1 <= s2     = True
_ `subset` _ = False

elementOf :: Extended -> Interval -> Bool
x `elementOf` (Interval i s) | i <= s = i <= x && x <= s
x `elementOf` (Interval i s) | i >= s = i <= x || x <= s

mergeInterval :: Interval -> Interval -> Interval
mergeInterval int1@(Interval i1 s1) int2@(Interval i2 s2) | i1 <= s1 && i2 <= s2 = Interval (min i1 i2) (max s1 s2)
                                                          | i1 >= s1 && i2 >= s2 && (i1 <= s2 || i2 <= s1) = Interval Infinity Infinity
                                                          | i1 >= s1 && i2 >= s2 = Interval (min i1 i2) (max s1 s2)
                                                          | i1 >= s1 && i2 <= s2 = mergeInterval int2 int1
                                                          | i1 <= s1 && i2 >= s2 = doTricky
  where doTricky | int1 `subset` int2         = int2
                 | i2 <= s1 && i1 <= s2       = Interval Infinity Infinity
                 | s1 /= Infinity && s1 <= i2 = Interval i2 s1
                 | s1 == Infinity             = Interval i1 s2
                 | i1 /= Infinity && s2 <= i1 = Interval i1 s2
                 | i1 == Infinity             = Interval i2 s1
