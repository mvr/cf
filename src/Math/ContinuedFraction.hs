{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Math.ContinuedFraction where

import Data.Maybe (catMaybes)
import Data.Ratio

import Debug.Trace

import Math.ContinuedFraction.Interval

data CF' a = CF [a]
type CF = CF' Integer

type Hom a = (a, a,
              a, a)

type Bihom a = (a, a, a, a,
                a, a, a, a)

class (Fractional (FractionField a)) => HasFractionField a where
  type FractionField a :: *
  insert :: a -> FractionField a
  extract :: FractionField a -> (a, a)

instance HasFractionField Integer where
  type FractionField Integer = Rational
  insert = fromInteger
  extract r = (numerator r, denominator r)

instance HasFractionField Rational where
  type FractionField Rational = Rational
  insert = id
  extract r = (numerator r % 1, denominator r % 1)

instance HasFractionField CF where
  type FractionField CF = CF
  insert = id
  extract r = (r, 1)

homEmit :: Num a => Hom a -> a -> Hom a
homEmit (n0, n1,
         d0, d1) x = (d0,        d1,
                      n0 - d0*x, n1 - d1*x)

homAbsorb :: Num a => Hom a -> a -> Hom a
homAbsorb (n0, n1,
           d0, d1) x = (n0*x + n1, n0,
                        d0*x + d1, d0)

det :: Num a => Hom a -> a
det (n0, n1,
     d0, d1) = n0 * d1 - n1 * d0

homEval :: (Num a, HasFractionField a, Eq (FractionField a)) => Hom a -> Extended (FractionField a) -> Extended (FractionField a)
homEval (n0, n1,
         d0, d1) (Finite q) | denom /= 0 = Finite $ num / denom
                            | num == 0 = error "0/0 in homQ"
                            | otherwise = Infinity
  where num   = insert n0 * q + insert n1
        denom = insert d0 * q + insert d1
homEval (n0, _n1,
         d0, _d1) Infinity = Finite $ insert n0 / insert d0


boundHom :: (Ord a, Num a, HasFractionField a, Eq (FractionField a)) => Hom a -> Interval (FractionField a) -> Interval (FractionField a)
boundHom h (Interval i s) | det h > 0 = Interval i' s'
                          | det h < 0 = Interval s' i'
                          | otherwise = error "0 det in boundHom"
  where i' = homEval h i
        s' = homEval h s

primitiveBound :: forall a. (Eq a, Num a, HasFractionField a) => a -> Interval (FractionField a)
primitiveBound 0 = Interval (Finite $ insert bot) (Finite $ insert top)
  where bot = (-2) :: a
        top = 2 :: a
primitiveBound n = Interval (Finite $ an - 0.5) (Finite $ 0.5 - an)
  where an = insert $ abs n



basePrimitiveBound :: HasFractionField a => FractionField a -> a -> Interval (FractionField a)
basePrimitiveBound sqrt3 n = Interval (Finite (i / denom)) (Finite (s / denom))
  where i = -4 * z + (z*z+1) * sqrt3
        s = -4 * z - (z*z+1) * sqrt3
        denom = z*z - 3
        z = insert n

instance HasPrimitiveBound Integer where
  primitiveBound n | abs n <= 1 = basePrimitiveBound sqrt3g n
    where sqrt3g = 1.74-- 3900231685776982 % 2251799813685248

  primitiveBound n | otherwise  = basePrimitiveBound sqrt3l n
    where sqrt3l = 1.73--3900231685776981 % 2251799813685248

instance HasPrimitiveBound CF where
  primitiveBound = basePrimitiveBound (CF $ 1 : cycle [1,2])

mysqrt3 = (CF $ 1 : cycle [1,2])

-- Need to check this
euclideanPart :: (RealFrac a1, Integral a) => Interval a1 -> a
euclideanPart (Interval Infinity Infinity) = 0
euclideanPart (Interval (Finite a) Infinity)
  | c > 0 = c
  | otherwise = 0
  where c = ceiling a
euclideanPart (Interval Infinity (Finite b))
  | f < 0 = f
  | otherwise = 0
  where f = floor b
euclideanPart i@(Interval (Finite a) (Finite b))
--  | a <= b && c > f = truncate a
  | abs c <= abs f  = c
  | otherwise       = f
  where c = ceiling a
        f = floor b

nthPrimitiveBounds :: (Ord a, Num a, HasFractionField a, Eq (FractionField a), HasPrimitiveBound a) =>
                       CF' a -> [Interval (FractionField a)]
nthPrimitiveBounds (CF cf) = zipWith boundHom homs (map primitiveBound cf) ++ repeat (Interval (Finite ev) (Finite ev))
  where homs = scanl homAbsorb (1,0,0,1) cf
        ev = evaluate (CF cf)

evaluate :: (HasFractionField a) => CF' a -> FractionField a
evaluate (CF []) = error "evaluate []"
evaluate (CF [c]) = insert c
evaluate (CF (c:cs)) = insert c + recip (evaluate (CF cs))

valueToCF :: RealFrac a => a -> CF
valueToCF r = if rest == 0 then
                CF [d]
              else
                let (CF ds)  = valueToCF (recip rest) in CF (d:ds)
  where (d, rest) = properFraction r


intervalThin :: (RealFrac a) => Interval a -> Bool
intervalThin (Interval Infinity    Infinity)  = False
intervalThin (Interval Infinity   (Finite _)) = False
intervalThin (Interval (Finite _)  Infinity)  = False
intervalThin (Interval (Finite x) (Finite y)) = 4 * (x - y)^2 < (1+x^2) * (1+y^2)

--existsEmittable :: (RealFrac a) => Interval a -> Maybe Integer
existsEmittable i = if intervalThin i then
                      Just $ euclideanPart i
                    else
                      Nothing

hom :: (Ord a, Num a, HasFractionField a, RealFrac (FractionField a), HasPrimitiveBound a) => Hom a -> CF' a -> CF
hom (_n0, _n1,
     0,   _d1) (CF []) = CF []
hom (n0, _n1,
     d0, _d1) (CF []) = valueToCF (insert n0 / insert d0)
hom h (CF (x:xs)) = case existsEmittable $ boundHom h (primitiveBound x) of
                     Just n ->  CF $ n : rest
                       where (CF rest) = hom (homEmit h (fromInteger n)) (CF (x:xs))
                     Nothing -> hom (homAbsorb h x) (CF xs)

bihomEmit :: Num a => Bihom a -> a -> Bihom a
bihomEmit (n0, n1, n2, n3,
           d0, d1, d2, d3) x = (d0,        d1,        d2,        d3,
                                n0 - d0*x, n1 - d1*x, n2 - d2*x, n3 - d3*x)

bihomAbsorbX :: Num a => Bihom a -> a -> Bihom a
bihomAbsorbX (n0, n1, n2, n3,
              d0, d1, d2, d3) x = (n0*x + n1, n0, n2*x + n3, n2,
                                   d0*x + d1, d0, d2*x + d3, d2)

bihomAbsorbY :: Num a => Bihom a -> a -> Bihom a
bihomAbsorbY (n0, n1, n2, n3,
              d0, d1, d2, d3) y = (n0*y + n2, n1*y + n3, n0, n1,
                                   d0*y + d2, d1*y + d3, d0, d1)

bihomSubstituteX :: (Num a, HasFractionField a) => Bihom a -> Extended (FractionField a) -> Hom a
bihomSubstituteX (n0, n1, n2, n3,
                  d0, d1, d2, d3) (Finite x) = (n0*num + n1*den, n2*num + n3*den,
                                                d0*num + d1*den, d2*num + d3*den)
  where (num, den) = extract x
bihomSubstituteX (n0, _n1, n2, _n3,
                  d0, _d1, d2, _d3) Infinity = (n0, n2,
                                                d0, d2)

bihomSubstituteY :: (Num a, HasFractionField a) => Bihom a -> Extended (FractionField a) -> Hom a
bihomSubstituteY (n0, n1, n2, n3,
                  d0, d1, d2, d3) (Finite y) = (n0*num + n2*den, n1*num + n3*den,
                                                d0*num + d2*den, d1*num + d3*den)
  where (num, den) = extract y
bihomSubstituteY (n0, n1, _n2, _n3,
                  d0, d1, _d2, _d3) Infinity = (n0, n1,
                                                d0, d1)

boundBihom :: (Ord a, Num a, HasFractionField a, Eq (FractionField a), Ord (FractionField a)) =>
              Bihom a -> Interval (FractionField a) -> Interval (FractionField a) -> Interval (FractionField a)
boundBihom bh x@(Interval ix sx) y@(Interval iy sy) = r1 `mergeInterval` r2 `mergeInterval` r3 `mergeInterval` r4
  where r1 = boundHom (bihomSubstituteX bh ix) y
        r2 = boundHom (bihomSubstituteY bh iy) x
        r3 = boundHom (bihomSubstituteX bh sx) y
        r4 = boundHom (bihomSubstituteY bh sy) x

select :: (Ord a, Num a, HasFractionField a, Eq (FractionField a), Ord (FractionField a)) =>
          Bihom a -> Interval (FractionField a) -> Interval (FractionField a) -> Bool
select bh x@(Interval ix sx) y@(Interval iy sy) = intY <= intX
  where intX = max r3 r4
        intY = max r1 r2
        r1 = boundHom (bihomSubstituteX bh ix) y
        r2 = boundHom (bihomSubstituteX bh sx) y
        r3 = boundHom (bihomSubstituteY bh iy) x
        r4 = boundHom (bihomSubstituteY bh sy) x

bihom :: (Ord a, Num a, HasFractionField a, HasPrimitiveBound a, RealFrac (FractionField a), Show a, Show (Interval (FractionField a)))
         => Bihom a -> CF' a -> CF' a -> CF
bihom bh (CF []) y = hom (bihomSubstituteX bh Infinity) y
bihom bh x (CF []) = hom (bihomSubstituteY bh Infinity) x
--bihom bh (CF (x:xs)) (CF (y:ys)) = case existsEmittable $ boundBihom bh (primitiveBound x) (primitiveBound y) of
bihom bh (CF (x:xs)) (CF (y:ys)) = let i = boundBihom bh (primitiveBound x) (primitiveBound y); e = existsEmittable i in case traceShow (bh, i, x, y, e) $ e of
                   Just n -> CF $ n : rest
                     where (CF rest) = bihom (bihomEmit bh (fromInteger n)) (CF (x:xs)) (CF (y:ys))
                   Nothing -> if select bh (primitiveBound x) (primitiveBound y) then
                                let bh' = bihomAbsorbX bh x in bihom bh' (CF xs) (CF (y:ys))
                              else
                                let bh' = bihomAbsorbY bh y in bihom bh' (CF (x:xs)) (CF ys)

instance Num CF where
  (+) = bihom (0, 1, 1, 0,
               0, 0, 0, 1)
  (-) = bihom (0, -1, 1, 0,
               0,  0, 0, 1)
  (*) = bihom (1, 0, 0, 0,
               0, 0, 0, 1)

  fromInteger n = CF [n]

instance Fractional CF where
  (/) = bihom (0, 0, 1, 0,
               0, 1, 0, 0)

  fromRational = valueToCF

base :: Integer
base = 10

rationalDigits :: Rational -> [Integer]
rationalDigits 0 = []
rationalDigits r = let d = num `quot` den in
                   d : rationalDigits (fromInteger base * (r - fromInteger d))
  where num = numerator r
        den = denominator r

digits :: CF -> [Integer]
digits = go (1, 0, 0, 1)
  where go (0, 0, _, _) _ = []
        go (p, _, q, _) (CF []) = rationalDigits (p % q)
        go h (CF (c:cs)) = case intervalDigit $ boundHom h (primitiveBound c) of
                            Nothing -> let h' = homAbsorb h c in go h' (CF cs)
                            Just d  -> d : go (homEmitDigit h d) (CF (c:cs))
        homEmitDigit (n0, n1,
                      d0, d1) d = (base * (n0 - d0*d), base * (n1 - d1*d),
                                   d0,                 d1)

cfString :: CF -> String
cfString cf = case digits cf of
               []     -> "Infinity"
               [i]    -> show i
               (i:is) -> show i ++ "." ++ concatMap show is

instance Show CF where
  show = take 50 . cfString

instance Eq CF where
  a == b = a `compare` b == EQ

instance Ord CF where
  a `compare` b = head $ catMaybes $ zipWith comparePosition (nthPrimitiveBounds a) (nthPrimitiveBounds b)

instance Real CF where

instance RealFrac CF where


cfcf :: CF' CF -> CF
cfcf = hom (1, 0, 0, 1)

-- 1496821043129 % 9898658119325
-- 2425236950707 % 4457308565364

-- [0,6,1,1,1,1,2,2,4,2,1,2,1,1,1,2,3,1,1,3,1,1,1,11,108,1,2,7,1,1,1,1,8]
-- [0,1,1,5,5,1,14,2,1,1,3,1,1,1,1,1,1,3,1,1,6,1,4,1,1,1,1,3,1,2,14,1,22,2]
