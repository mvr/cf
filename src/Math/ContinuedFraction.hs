{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Math.ContinuedFraction (
  CF,
  cfString,
  cfcf
) where

import Data.Maybe (catMaybes, mapMaybe)
import Data.Ratio

import Math.ContinuedFraction.Interval

newtype CF' a = CF [a]
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

constantFor :: (Eq a, Num a, HasFractionField a) => Hom a -> Extended (FractionField a)
constantFor (_, _,
             0, 0) = Infinity
constantFor (0, 0,
             0, _) = Finite 0
constantFor (0, 0,
             _, 0) = Finite 0
constantFor (a, 0,
             b, 0) = Finite (insert a / insert b)
constantFor (_, a,
             _, b) = Finite (insert a / insert b)

boundHom :: (Ord a, Num a, HasFractionField a, Eq (FractionField a)) => Hom a -> Interval (FractionField a) -> Interval (FractionField a)
boundHom h (Interval i s) | det h > 0 = Interval i' s'
                          | det h < 0 = Interval s' i'
                          | otherwise = Interval c c
  where i' = homEval h i
        s' = homEval h s
        c = constantFor h

primitiveBound :: forall a. (Ord a, Num a, HasFractionField a) => a -> Interval (FractionField a)
primitiveBound n | abs n < 1 = Interval (Finite $ insert bot) (Finite $ insert top)
  where bot = (-2) :: a
        top = 2 :: a
primitiveBound n = Interval (Finite $ an - 0.5) (Finite $ 0.5 - an)
  where an = insert $ abs n

-- TODO: just take the rational answer from the hom
nthPrimitiveBounds :: (Ord a, Num a, HasFractionField a, Eq (FractionField a)) =>
                       CF' a -> [Interval (FractionField a)]
nthPrimitiveBounds (CF cf) = zipWith boundHom homs (map primitiveBound cf) ++ repeat (Interval ev ev)
  where homs = scanl homAbsorb (1,0,0,1) cf
        ev = evaluate (CF cf)

evaluate :: (HasFractionField a, Eq (FractionField a)) => CF' a -> Extended (FractionField a)
evaluate (CF []) = Infinity
evaluate (CF [c]) = Finite $ insert c
evaluate (CF (c:cs)) = case next of
                        (Finite 0) -> Infinity
                        Infinity   -> Finite $ insert c
                        (Finite r) -> Finite $ insert c + recip r
  where next = evaluate (CF cs)

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
intervalThin (Interval (Finite i) (Finite s)) = abs z > 3 || abs (zi - zs) < 2
  where zi = round i
        zs = round s
        z  = if abs zs < abs zi then zs else zi

euclideanPart :: (RealFrac a, Integral b) => Interval a -> Maybe b
euclideanPart (Interval Infinity    Infinity)  = undefined
euclideanPart (Interval Infinity   (Finite b)) = Just $ floor b
euclideanPart (Interval (Finite a)  Infinity)  = Just $ ceiling a
euclideanPart i@(Interval (Finite a) (Finite b))
  | 0 `elementOf` i && not subsetZero = Nothing
  | zi /= 0 && zs /= 0 = Just z
  | subsetZero = Just 0
  | otherwise = Nothing
    where zi = round a
          zs = round b
          z  = if abs zs < abs zi then zs else zi
          subsetZero = i `subset` Interval (Finite (-2)) (Finite 2)

existsEmittable :: RealFrac a => Interval a -> Maybe Integer
existsEmittable i = if intervalThin i then
                      euclideanPart i
                    else
                      Nothing

hom :: (Ord a, Num a, HasFractionField a, RealFrac (FractionField a)) => Hom a -> CF' a -> CF
hom (_n0, _n1,
     0,   0) _  = CF []
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
select bh x@(Interval ix sx) y@(Interval iy sy) = intX `smallerThan` intY
  where intX = if r1 `smallerThan` r2 then r2 else r1
        intY = if r3 `smallerThan` r4 then r3 else r4
        r1 = boundHom (bihomSubstituteX bh ix) y
        r2 = boundHom (bihomSubstituteX bh sx) y
        r3 = boundHom (bihomSubstituteY bh iy) x
        r4 = boundHom (bihomSubstituteY bh sy) x

bihom :: (Ord a, Num a, HasFractionField a, RealFrac (FractionField a))
         => Bihom a -> CF' a -> CF' a -> CF
bihom bh (CF []) y = hom (bihomSubstituteX bh Infinity) y
bihom bh x (CF []) = hom (bihomSubstituteY bh Infinity) x
bihom bh (CF (x:xs)) (CF (y:ys)) = case existsEmittable $ boundBihom bh (primitiveBound x) (primitiveBound y) of
                   Just n -> CF $ n : rest
                     where (CF rest) = bihom (bihomEmit bh (fromInteger n)) (CF (x:xs)) (CF (y:ys))
                   Nothing -> if select bh (primitiveBound x) (primitiveBound y) then
                                let bh' = bihomAbsorbX bh x in bihom bh' (CF xs) (CF (y:ys))
                              else
                                let bh' = bihomAbsorbY bh y in bihom bh' (CF (x:xs)) (CF ys)

homchain :: [Hom Integer] -> CF
homchain (h:h':hs) = case quotEmit h of
                     Just n ->  CF $ n : rest
                       where (CF rest) = homchain ((homEmit h n):h':hs)
                     Nothing -> homchain ((h `mult` h'):hs)
  where quotEmit (n0, n1,
                  d0, d1) = if d0 /= 0 && d1 /= 0 && n0 `quot` d0 == n1 `quot` d1 then Just $ n0 `quot` d0 else Nothing
        mult (n0, n1,
              d0, d1)
             (n0', n1',
              d0', d1') =(n0*n0' + n1*d0', n0*n1' + n1*d1',
                          d0*n0' + d1*d0', d0*n1' + d1*d1')

instance Num CF where
  (+) = bihom (0, 1, 1, 0,
               0, 0, 0, 1)
  (-) = bihom (0, -1, 1, 0,
               0,  0, 0, 1)
  (*) = bihom (1, 0, 0, 0,
               0, 0, 0, 1)

  fromInteger n = CF [n]

  signum x = case 0 `compare` x of
              EQ -> 0
              LT -> 1
              GT -> -1

  abs x | x < 0     = -x
        | otherwise = x

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
cfString (CF []) = "Infinity"
cfString cf | cf < 0 = '-' : cfString (-cf)
cfString cf = case digits cf of
               []     -> "0"
               [i]    -> show i
               (i:is) -> show i ++ "." ++ concatMap show is

instance Show CF where
  show = take 50 . cfString

instance Eq CF where
  a == b = a `compare` b == EQ

instance Ord CF where
  a `compare` b = head $ catMaybes $ zipWith comparePosition (nthPrimitiveBounds a) (nthPrimitiveBounds b)

instance Real CF where
  toRational = error "CF: toRational"

instance RealFrac CF where
  properFraction cf = head $ mapMaybe checkValid $ nthPrimitiveBounds cf
    where checkValid (Interval (Finite a) (Finite b)) = if a <= b && truncate a == truncate b then
                                                          Just (truncate a, cf - fromInteger (truncate a))
                                                        else
                                                          Nothing
          checkValid _ = Nothing

cfcf :: CF' CF -> CF
cfcf = hom (1, 0, 0, 1)

instance Floating CF where
  pi = homchain ((0,4,1,0) : map go [1..])
    where go n = (2*n-1, n^2,
                  1,     0)

  exp r = cfcf (CF $ 1 : concatMap go [0..])
    where go n = [fromInteger (4*n+1) / r,
                  -2,
                  -fromInteger (4*n+3) / r,
                  2]

  -- TODO: restrict range
  log r = cfcf (CF $ 0 : concatMap go [0..])
    where go n = [fromInteger (2*n+1) / (r-1),
                  fromRational $ 2 % (n+1)]

  tan r = cfcf (CF $ 0 : concatMap go [0..])
    where go n = [fromInteger (4*n+1) / r,
                  -fromInteger (4*n+3) / r]

  sin r = bihom (0,2,0,0,
                 1,0,0,1) tanhalf tanhalf
    where tanhalf = tan (r / 2)

  cos r = bihom (-1,0,0,1,
                  1,0,0,1) tanhalf tanhalf
    where tanhalf = tan (r / 2)

  sinh r = bihom (1,0,0,-1,
                  0,1,1, 0) expr expr
    where expr = exp r

  cosh r = bihom (1,0,0,1,
                  0,1,1,0) expr expr
    where expr = exp r

  tanh r = bihom (1,0,0,-1,
                  1,0,0, 1) expr expr
    where expr = exp r
