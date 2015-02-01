module Math.ContinuedFraction.Effective where

import Control.Applicative
import Data.Maybe (listToMaybe)
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
homAbsorb hom xs = (foldl homAbsorbOne hom (take (fromInteger n) xs'), drop (fromInteger n) xs')
  where (n, xs') = absorbHowMany xs

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

hom :: Hom -> CF -> CF
hom h xs = case existsEmittable $ boundHom h (bound xs) of
            Just n ->  n : hom (homEmit h n) xs
            Nothing -> hom h' xs'
              where (h', xs') = homAbsorb h xs



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
existsEmittable i = listToMaybe $ filter (\n -> i `subset` primitiveBound n) (candidates i)

topCandidates :: Interval -> [Integer]
topCandidates (Interval (Finite r) _) = [round r, - floor (r - 0.5)]
topCandidates (Interval Infinity _) = []

botCandidates :: Interval -> [Integer]
botCandidates (Interval _ (Finite r)) = [round r, - ceiling (r + 0.5)]
botCandidates (Interval _ Infinity) = []

candidates :: Interval -> [Integer]
candidates i = topCandidates i ++ botCandidates i

absorbHowMany :: CF -> (Integer, CF)
absorbHowMany xs = (min n m, xs')
  where (n, m, xs') = d xs

d :: CF -> (Integer, Integer, CF)
d xs@(x0 : 2 : x2 : _)                 | abs x0 == 1 && (x2 >= 3 || x2 == 1 || x2 <= -4)            = (2, 2, xs)
d xs@(x0 : 2 : 2  : x3 : _)            | abs x0 == 1 && (x3 >= 1 || x3 <= -3)                       = (3, 3, xs)
d xs@(x0 : 2 : 2  : -2 : _)            | abs x0 == 1                                                = (2, 3, xs)
d xs@(x0 : 2 : -2 : -1 : 2  : x5 : _)  | abs x0 == 1 && (x5 == 2 || x5 == -2 || x5 == -3)           = (3, 5, xs)
d xs@(x0 : 2 : -2 : -1 : 2  : x5 : _)  | abs x0 == 1 && (x5 >= 3 || x5 == 1 || x5 <= -4)            = (5, 5, xs)
d xs@(x0 : 2 : -2 : -1 : x4 : -2 : _)  | abs x0 == 1 && x4 >= 3                                     = (4, 5, xs)
d xs@(x0 : 2 : -2 : -1 : x4 : x5 : _)  | abs x0 == 1 && x4 >= 3 && (x5 >= 1 || x5 <= -3)            = (5, 5, xs)
d xs@(x0 : 2 : -3 : -1 : _)            | abs x0 == 1                                                = (3, 3, xs)
d xs@(x0 : 2 : -3 : x3 : 2  : _)       | abs x0 == 1 && x3 <= -2                                    = (3, 4, xs)
d xs@(x0 : 2 : -3 : x3 : x4 : _)       | abs x0 == 1 && x3 <= -2 && (x4 >= 3 || x4 <= -1)           = (4, 4, xs)
d xs@(x0 : 2 : 1  : _)                 | x0 == 0 || x0 <= -2                                        = (2, 2, xs)
d xs@(x0 : 2 : x2 : -2 : _)            | (x0 == 0 || x0 <= -2) && x2 >= 2                           = (2, 3, xs)
d xs@(x0 : 2 : x2 : x3 : _)            | (x0 == 0 || x0 <= -2) && x2 >= 2 && (x3 >= 1 || x3 <= -3)  = (3, 3, xs)

d (x0 :  0 : x2 : xs)                          = (0, 0, (x0+x2) : xs)
d (x0 :  2 :  0 : x3 : xs)                     = d (x0 : x3+2 : xs)
d (x0 : -2 :  0 : x3 : xs)                     = d (x0 : x3-2 : xs)
d (x0 : x1 :  0 : x3 : xs)                     = (1, 0, x0 : (x1+x3) : xs)
d (x0 :  2 :  2 :  0 : -5 : xs)                = d (x0 : 2 : -3 : xs)
d (x0 :  2 : x2 :  0 : x4 : xs)                = (2, 0, x0 : 2 : (x2+x4) : xs)
d (x0 :  2 : x2 : -2 :  0 : x5 : xs)           = d (x0 : 2 : x2 : x5-2 : xs)
d (x0 :  2 : -3 : x3 :  0 : x5 : xs)           = (3, 0, x0 : 2 : -3 : (x3+x5) : xs)
d (x0 :  2 : -2 : -1 :  2 :  0 : x6 : xs)      = d (x0 : 2 : -2 : -1 : x6+2 : xs)
d (x0 :  2 : -2 : -1 : x4 :  0 : x6 : xs)      = (4, 0, x0 : 2 : -2 : -1 : (x4+x6) : xs)
d (x0 :  2 : -2 : -1 :  2 :  2 :  0 : x7 : xs) = d (x0 : 2 : -2 : -1 : 2 : x7+2 :  xs)
d (x0 :  2 : -2 : -1 : x4 : -2 :  0 : x7 : xs) = d (x0 : 2 : -2 : -1 : x4 : x7-2 :  xs)
d (x0 :  2 : -2 : -1 :  2 : -3 :  0 : x7 : xs) = d (x0 : 2 : -2 : -1 : 2 : x7-3 :  xs)

d xs@(_ : -2  : _) = (j, i, xs)
  where (i, j, _) = d $ map negate xs
d xs = (1, 1, xs)

bound :: CF -> Interval
bound xs = Interval i s
  where (n, m, xs') = d xs
        Interval i _ = nthPrimitiveBound xs' n
        Interval _ s = nthPrimitiveBound xs' m

nextBound :: CF -> Interval
nextBound xs = if a == 0 then
                 bound xs'
               else
                 go a xs'
  where (n, m, xs') = d xs
        a = min n m
        go 0 cs = bound cs
        go i (c:cs) = c .+ recips (go (i-1) cs)

double :: Hom
double = (2, 0,
          0, 1)

sqrt2 :: CF
sqrt2 = 1 : repeat 2

exp1 :: CF
exp1 = 2 : concatMap triple [1..]
  where triple n = [1, 2 * n, 1]
