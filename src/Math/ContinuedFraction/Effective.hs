module Math.ContinuedFraction.Effective where

import Data.Ratio

import Math.ContinuedFraction.Interval

type CF = [Integer]

type Hom = (Integer, Integer,
            Integer, Integer)

homQ :: Hom -> Extended -> Extended
homQ (n0, n1,
      d0, d1) (Finite q) | denom /= 0 = Finite $ num / denom
                         | num == 0 = undefined
                         | otherwise = Infinity
  where num   = fromInteger n0 * q + fromInteger n1
        denom = fromInteger d0 * q + fromInteger d1
homQ (n0, n1,
      d0, d1) _ = Finite $ n0 % d0

homEmit :: Hom -> Integer -> Hom
homEmit (n0, n1,
         d0, d1) x = (d0,        d1,
                      n0 - d0*x, n1 - d1*x)

homAbsorb :: Hom -> CF -> (Hom, CF)
homAbsorb hom xs = (foldl homAbsorbOne hom (take n xs), drop n xs)
  where n = fromInteger $ absorbHowMany xs

homAbsorbOne :: Hom -> Integer -> Hom
homAbsorbOne (n0, n1,
              d0, d1) x = (n0*x + n1, n0,
                           d0*x + d1, d0)

det :: Hom -> Integer
det (n0, n1,
     d0, d1) = n0 * d1 - n1 * d0

boundHom :: Hom -> Interval -> Interval
boundHom h (Interval i s) | det h > 0 = Interval i' s'
                          | det h < 0 = Interval s' i'
                          | otherwise = undefined
  where i' = homQ h i
        s' = homQ h s

primitiveBound :: Integer -> Interval
primitiveBound   0  = Interval (-0.5) 0.5
primitiveBound (-1) = Interval (-1.6) (-0.4)
primitiveBound   1  = Interval 0.4    1.6
primitiveBound x | x <= -2 = Interval (-(fromInteger x) + 0.5) ((fromInteger x) + 0.5)
primitiveBound x | x >= 2 = Interval ((fromInteger x) - 0.5) (-(fromInteger x) - 0.5)

nthPrimitiveBound :: CF -> Integer -> Interval
nthPrimitiveBound (c:_) 0 = primitiveBound c
nthPrimitiveBound (c:cs) n = c .+ recips (nthPrimitiveBound cs (n-1))
nthPrimitiveBound [] _ = undefined

existsEmittable :: Interval -> Maybe Integer
existsEmittable i | i `subset` Interval (-1.6) (-0.4) = Just (-1)
                  | i `subset` Interval 0.4    1.6    = Just 1
                  | i `subset` Interval (-0.5) 0.5    = Just 0
existsEmittable i = undefined
existsEmittable _ = Nothing

absorbHowMany :: CF -> Integer
absorbHowMany cs = undefined

d :: CF -> (Integer, Integer)
d = undefined

bound :: CF -> Interval
bound = undefined

nextBound :: CF -> Interval
nextBound = undefined

sqrt2 :: CF
sqrt2 = 1 : repeat 2

exp1 :: CF
exp1 = 2 : concatMap triple [1..]
  where triple n = [1, 2 * n, 1]
