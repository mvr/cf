{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-- |
-- A continued fraction whose terms may be positive, negative or
-- zero. The methods in @Floating@ are supported, with the exception
-- of @asin@, @acos@ and @atan@.
module Math.ContinuedFraction (
  CF,
  CF'(..),
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
  frac :: (a, a) -> FractionField a
  extract :: FractionField a -> (a, a)

instance HasFractionField Integer where
  type FractionField Integer = Rational
  insert = fromInteger
  {-# INLINE insert #-}
  frac = uncurry (%)
  {-# INLINE frac #-}
  extract r = (numerator r, denominator r)
  {-# INLINE extract #-}

instance HasFractionField Rational where
  type FractionField Rational = Rational
  insert = id
  {-# INLINE insert #-}
  frac = uncurry (/)
  {-# INLINE frac #-}
  extract r = (numerator r % 1, denominator r % 1)
  {-# INLINE extract #-}

instance HasFractionField CF where
  type FractionField CF = CF
  insert = id
  {-# INLINE insert #-}
  frac = uncurry (/)
  {-# INLINE frac #-}
  extract r = (r, 1)
  {-# INLINE extract #-}

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

homEval :: (Eq a, Num a, HasFractionField a) => Hom a -> Extended (FractionField a) -> Extended (FractionField a)
homEval (n0, n1,
         d0, d1) (Finite q) | denom /= 0 = Finite $ frac (num, denom)
                            | num == 0 = error "0/0 in homQ"
                            | otherwise = Infinity
  where (qnum, qdenom) = extract q
        num   = n0 * qnum + n1 * qdenom
        denom = d0 * qnum + d1 * qdenom
homEval (n0, _n1,
         d0, _d1) Infinity = Finite $ frac (n0, d0)

constantFor :: (Eq a, Num a, HasFractionField a) => Hom a -> Extended (FractionField a)
constantFor (_, _,
             0, 0) = Infinity
constantFor (0, 0,
             0, _) = Finite 0
constantFor (0, 0,
             _, 0) = Finite 0
constantFor (a, 0,
             b, 0) = Finite $ frac (a, b)
constantFor (_, a,
             _, b) = Finite $ frac (a, b)

boundHom :: (Ord a, Num a, HasFractionField a, Eq (FractionField a), Ord (FractionField a))
         => Hom a -> Interval (FractionField a) -> Interval (FractionField a)
boundHom (_, _,
          0, 0) _ = Empty
boundHom h int | det h > 0 = interval i' s'
               | det h < 0 = interval s' i'
               | otherwise = interval c c
  where i' = homEval h (leftStart int)
        s' = homEval h (rightStart int)
        c = constantFor h

primitiveBound :: forall a. (Ord a, Num a, HasFractionField a) => a -> Interval (FractionField a)
primitiveBound n | abs n < 1 = Inside (insert bot) (insert top)
  where bot = (-2) :: a
        top = 2 :: a
primitiveBound n = Outside (0.5 - an) (an - 0.5)
  where an = insert $ abs n

-- TODO: just take the rational answer from the hom
nthPrimitiveBounds :: (Ord a, Num a, HasFractionField a, Eq (FractionField a), Ord (FractionField a)) =>
                       CF' a -> [Interval (FractionField a)]
nthPrimitiveBounds (CF cf) = zipWith boundHom homs (map primitiveBound cf) ++ repeat (Inside ev ev)
  where homs = scanl homAbsorb (1,0,0,1) cf
        ev = evaluate (CF cf)

evaluate :: (Num a, Eq a, HasFractionField a, Eq (FractionField a)) => CF' a -> FractionField a
evaluate (CF []) = undefined
evaluate (CF [c, _, 0]) = insert c
evaluate (CF [c]) = insert c
evaluate (CF (c:cs)) = insert c + recip (evaluate (CF cs))

valueToCF :: RealFrac a => a -> CF
valueToCF r = if rest == 0 then
                CF [d]
              else
                let (CF ds)  = valueToCF (recip rest) in CF (d:ds)
  where (d, rest) = properFraction r

existsEmittable :: (RealFrac a, Integral b) => Interval a -> Maybe b
existsEmittable (LeftInfinite _) = Nothing -- TODO
existsEmittable (RightInfinite _) = Nothing
existsEmittable int@(Inside a b) = euclideanCheck int a b
existsEmittable int@(Outside a b) = euclideanCheck int a b
existsEmittable _ = Nothing

euclideanCheck :: (Num a, Ord a, RealFrac a, Integral b) => Interval a -> a -> a -> Maybe b
euclideanCheck int a b
  | not isThin = Nothing
  | 0 `elementOf` int && not subsetZero = Nothing
  | zi /= 0 && zs /= 0 = Just z
  | subsetZero = Just 0
  | otherwise = Nothing
    where zi = round a
          zs = round b
          z  = if abs zs < abs zi then zs else zi
          isThin = abs z > 3 || abs (zi - zs) < 2
          subsetZero = int `subset` Inside (-2) 2

hom :: (Ord a, Num a, HasFractionField a, RealFrac (FractionField a)) => Hom a -> CF' a -> CF
hom (_n0, _n1,
     0,   0) _  = CF []
hom (_n0, _n1,
     0,   _d1) (CF []) = CF []
hom (n0, _n1,
     d0, _d1) (CF []) = valueToCF $ frac (n0, d0)
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

boundBihomAndSelect :: (Ord a, Num a, HasFractionField a, Eq (FractionField a), Ord (FractionField a)) =>
                       Bihom a -> Interval (FractionField a) -> Interval (FractionField a) -> (Interval (FractionField a), Bool)
boundBihomAndSelect bh x y = (interval, intX `smallerThan` intY)
  where interval = ixy `mergeInterval` iyx `mergeInterval` sxy `mergeInterval` syx
        ix  = leftStart x
        sx  = rightStart x
        iy  = leftStart y
        sy  = rightStart y
        ixy = boundHom (bihomSubstituteX bh ix) y
        iyx = boundHom (bihomSubstituteY bh iy) x
        sxy = boundHom (bihomSubstituteX bh sx) y
        syx = boundHom (bihomSubstituteY bh sy) x
        intX = if ixy `smallerThan` sxy then sxy else ixy
        intY = if iyx `smallerThan` syx then syx else iyx

bihom :: (Ord a, Num a, HasFractionField a, RealFrac (FractionField a))
      => Bihom a -> CF' a -> CF' a -> CF
bihom bh (CF []) y = hom (bihomSubstituteX bh Infinity) y
bihom bh x (CF []) = hom (bihomSubstituteY bh Infinity) x
bihom bh (CF (x:xs)) (CF (y:ys)) =
  let (bound, which) = boundBihomAndSelect bh (primitiveBound x) (primitiveBound y) in
  case existsEmittable bound of
    Just n -> CF $ n : rest
      where (CF rest) = bihom (bihomEmit bh (fromInteger n)) (CF (x:xs)) (CF (y:ys))
    Nothing -> if which then
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

-- | Produce the (possibly infinite) decimal expansion of a continued
-- fraction
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
    where checkValid (Inside a b) = if truncate a == truncate b then
                                      Just (truncate a, cf - fromInteger (truncate a))
                                    else
                                      Nothing
          checkValid _ = Nothing

-- | Convert a continued fraction whose terms are continued fractions
-- into an ordinary continued fraction with integer terms
cfcf :: CF' CF -> CF
cfcf = hom (1, 0, 0, 1)

instance Floating CF where
  pi = homchain ((0,4,1,0) : map go [1..])
    where go n = (2*n-1, n^2,
                  1,     0)

  exp r | r < -1 || r > 1 = (exp (r / 2))^2
  exp r = cfcf (CF $ 1 : concatMap go [0..])
    where go n = [fromInteger (4*n+1) / r,
                  -2,
                  -fromInteger (4*n+3) / r,
                  2]

  log r | r < 0.5 = log (2 * r) - log 2
  log r | r > 2   = log (r / 2) + log 2
  log r = cfcf (CF $ 0 : concatMap go [0..])
    where go n = [fromInteger (2*n+1) / (r-1),
                  fromRational $ 2 % (n+1)]

  tan r | r < -1 || r > 1 = bihom ( 0,1,1,0,
                                   -1,0,0,1) tanhalf tanhalf
    where tanhalf = tan (r / 2)
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
