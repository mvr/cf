module Math.ContinuedFraction.Effective where

import Data.Maybe (listToMaybe)
import Data.Ratio

import Math.ContinuedFraction.Interval

newtype CF = CF [Integer]
type CF' = [Integer]

type Hom = (Integer, Integer,
            Integer, Integer)

type Bihom = (Integer, Integer, Integer, Integer,
              Integer, Integer, Integer, Integer)

homQ :: Hom -> Extended -> Extended
homQ (n0, n1,
      d0, d1) (Finite q) | denom /= 0 = Finite $ num / denom
                         | num == 0 = error "0/0 in homQ"
                         | otherwise = Infinity
  where num   = fromInteger n0 * q + fromInteger n1
        denom = fromInteger d0 * q + fromInteger d1
homQ (n0, _n1,
      d0, _d1) Infinity = Finite $ n0 % d0

homEmit :: Hom -> Integer -> Hom
homEmit (n0, n1,
         d0, d1) x = (d0,        d1,
                      n0 - d0*x, n1 - d1*x)

homAbsorb :: Hom -> CF' -> (Hom, CF')
homAbsorb h xs = (foldl homAbsorbOne h (take (fromInteger n) xs'), drop (fromInteger n) xs')
  where (n, xs') = absorbHowMany xs

homAbsorbOne :: Hom -> Integer -> Hom
homAbsorbOne (n0, n1,
              d0, d1) x = (n0*x + n1, n0,
                           d0*x + d1, d0)

det :: Hom -> Integer
det (n0, n1,
     d0, d1) = n0 * d1 - n1 * d0

cfFromRational :: Rational -> CF'
cfFromRational r = if den == 1 then
                     [num]
                   else
                     d : cfFromRational (recip $ r - fromInteger d)
  where num = numerator r
        den = denominator r
        d = num `quot` den

boundHom :: Hom -> Interval -> Interval
boundHom h (Interval i s) | det h > 0 = Interval i' s'
                          | det h < 0 = Interval s' i'
                          | otherwise = error "0 det in boundHom"
  where i' = homQ h i
        s' = homQ h s

hom' :: Hom -> CF' -> CF'
hom' (_n0, _n1,
      0,   _d1) [] = []
hom' (n0, _n1,
      d0, _d1) [] = cfFromRational (n0 % d0)
hom' h xs = case existsEmittable $ boundHom h (bound xs) of
            Just n ->  n : hom' (homEmit h n) xs
            Nothing -> hom' h' xs'
              where (h', xs') = homAbsorb h xs

hom :: Hom -> CF -> CF
hom bh (CF xs) = CF $ hom' bh xs

bihomEmit :: Bihom -> Integer -> Bihom
bihomEmit (n0, n1, n2, n3,
           d0, d1, d2, d3) x = (d0,        d1,        d2,        d3,
                                n0 - d0*x, n1 - d1*x, n2 - d2*x, n3 - d3*x)

bihomAbsorbOneX :: Bihom -> Integer -> Bihom
bihomAbsorbOneX (n0, n1, n2, n3,
                 d0, d1, d2, d3) x = (n0*x + n1, n0, n2*x + n3, n2,
                                      d0*x + d1, d0, d2*x + d3, d2)

bihomAbsorbOneY :: Bihom -> Integer -> Bihom
bihomAbsorbOneY (n0, n1, n2, n3,
                 d0, d1, d2, d3) y = (n0*y + n2, n1*y + n3, n0, n1,
                                      d0*y + d2, d1*y + d3, d0, d1)

bihomAbsorbX :: Bihom -> CF' -> (Bihom, CF')
bihomAbsorbX bh xs = (foldl bihomAbsorbOneX bh (take (fromInteger n) xs'), drop (fromInteger n) xs')
  where (n, xs') = absorbHowMany xs

bihomAbsorbY :: Bihom -> CF' -> (Bihom, CF')
bihomAbsorbY bh ys = (foldl bihomAbsorbOneY bh (take (fromInteger n) ys'), drop (fromInteger n) ys')
  where (n, ys') = absorbHowMany ys

bihomSubstituteX :: Bihom -> Extended -> Hom
bihomSubstituteX (n0, n1, n2, n3,
                  d0, d1, d2, d3) (Finite x) = (n0*num + n1*den, n2*num + n3*den,
                                                d0*num + d1*den, d2*num + d3*den)
  where num = numerator x
        den = denominator x
bihomSubstituteX (n0, _n1, n2, _n3,
                  d0, _d1, d2, _d3) Infinity = (n0, n2,
                                                d0, d2)

bihomSubstituteY :: Bihom -> Extended -> Hom
bihomSubstituteY (n0, n1, n2, n3,
                  d0, d1, d2, d3) (Finite y) = (n0*num + n2*den, n1*num + n3*den,
                                                d0*num + d2*den, d1*num + d3*den)
  where num = numerator y
        den = denominator y
bihomSubstituteY (n0, n1, _n2, _n3,
                  d0, d1, _d2, _d3) Infinity = (n0, n1,
                                                d0, d1)

boundBihom :: Bihom -> Interval -> Interval -> Interval
boundBihom bh x@(Interval ix sx) y@(Interval iy sy) = r1 `mergeInterval` r2 `mergeInterval` r3 `mergeInterval` r4
  where r1 = boundHom (bihomSubstituteX bh ix) y
        r2 = boundHom (bihomSubstituteY bh iy) x
        r3 = boundHom (bihomSubstituteX bh sx) y
        r4 = boundHom (bihomSubstituteY bh sy) x

select :: Bihom -> Interval -> Interval -> Bool
select bh x@(Interval ix sx) y@(Interval iy sy) = intY <= intX
  where intX = max r3 r4
        intY = max r1 r2
        r1 = boundHom (bihomSubstituteX bh ix) y
        r2 = boundHom (bihomSubstituteX bh sx) y
        r3 = boundHom (bihomSubstituteY bh iy) x
        r4 = boundHom (bihomSubstituteY bh sy) x

bihom' :: Bihom -> CF' -> CF' -> CF'
bihom' bh [] ys = hom' (bihomSubstituteX bh Infinity) ys
bihom' bh xs [] = hom' (bihomSubstituteY bh Infinity) xs
bihom' bh xs ys = case existsEmittable $ boundBihom bh (bound xs) (bound ys) of
                  Just n  -> n : bihom' (bihomEmit bh n) xs ys
                  Nothing -> if select bh (bound xs) (bound ys) then
                               let (bh', xs') = bihomAbsorbX bh xs in bihom' bh' xs' ys
                             else
                               let (bh', ys') = bihomAbsorbY bh ys in bihom' bh' xs ys'

bihom :: Bihom -> CF -> CF -> CF
bihom bh (CF xs) (CF ys) = CF $ bihom' bh xs ys

primitiveBound :: Integer -> Interval
primitiveBound   0  = Interval (-0.5) 0.5
primitiveBound (-1) = Interval (-1.6) (-0.4)
primitiveBound   1  = Interval 0.4    1.6
primitiveBound x | x <= -2 = Interval (-(fromInteger x) + 0.5) ((fromInteger x) + 0.5)
primitiveBound x | x >= 2 = Interval ((fromInteger x) - 0.5) (-(fromInteger x) - 0.5)

evaluate :: CF' -> Rational
evaluate [c] = fromInteger c
evaluate (c:cs) = fromInteger c + recip (evaluate cs)

nthPrimitiveBounds :: CF' -> [Interval]
nthPrimitiveBounds cf = zipWith boundHom homs (map primitiveBound cf) ++ repeat (Interval (Finite ev) (Finite ev))
  where homs = scanl homAbsorbOne (1,0,0,1) cf
        ev = evaluate cf

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

emittableRange :: Interval -> [Integer]
emittableRange i = case cs of
                    [] -> []
                    _  -> [minimum cs .. maximum cs]
  where cs = filter (\n -> i `subset` primitiveBound n) (candidates i)

existsRestrictedEmittable :: Interval -> Integer -> Integer -> Maybe Integer
existsRestrictedEmittable int n m = listToMaybe $ traceShowId [ i | i <- blended, abs n < abs (n + i), int `subset` primitiveBound (n + i) ]
  where range = [2..(abs m)]
        blended = blend range (map negate range)
        blend (x:xs) ys = x : blend ys xs
        blend [] ys = ys

data State = Normal | Stored Integer | Zero Integer deriving (Show)

-- homz :: State -> Hom -> CF' -> CF'
-- -- todo verify this works
-- homz _ (_n0, _n1,
--         0,   _d1) [] = []
-- homz _ (n0, _n1,
--         d0, _d1) [] = cfFromRational (n0 % d0)

-- --homz status h xs | traceShow (status, h) False = undefined

-- homz Normal h xs = case existsEmittable $ boundHom h (bound xs) of
--                      Just n ->  if abs n <= 1 then
--                                   n : homz Normal (homEmit h n) xs
--                                 else
--                                   n : homz (Stored n) h xs
--                      Nothing -> homz Normal h' xs'
--                        where (h', xs') = homAbsorb h xs

-- homz (Stored n) h xs = case existsEmittable $ boundHom (homEmit h n) (bound xs) of
--                         Just m -> if m == 0 then
--                                     m : homz (Zero n) h xs
--                                   else
--                                     m : homz Normal (homEmit (homEmit h n) m) xs
--                         Nothing -> homz (Stored n) h' xs'
--                           where (h', xs') = homAbsorb h xs

-- homz (Zero n) h xs = case existsEmittable $ boundHom (homEmit (homEmit h n) 0) (bound xs) of
--                        Just m -> case existsRestrictedEmittable (boundHom (homEmit (homEmit h n) 0) (bound xs)) n m of
--                          Just i -> (i-n) : homz (Stored (n+i)) h xs
--                          Nothing -> homz (Zero n) h' xs'
--                        Nothing -> homz (Zero n) h' xs'
--                      where (h', xs') = homAbsorb h xs

absorbHowMany :: CF' -> (Integer, CF')
absorbHowMany xs = (min n m, xs')
  where (n, m, xs') = d xs

d :: CF' -> (Integer, Integer, CF')
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

-- d (x0 :  0 : x2 : xs)                          = (0, 0, (x0+x2) : xs)
-- d (x0 :  2 :  0 : x3 : xs)                     = d (x0 : x3+2 : xs)
-- d (x0 : -2 :  0 : x3 : xs)                     = d (x0 : x3-2 : xs)
-- d (x0 : x1 :  0 : x3 : xs)                     = (1, 0, x0 : (x1+x3) : xs)
-- d (x0 :  2 :  2 :  0 : -5 : xs)                = d (x0 : 2 : -3 : xs)
-- d (x0 :  2 : x2 :  0 : x4 : xs)                = (2, 0, x0 : 2 : (x2+x4) : xs)
-- d (x0 :  2 : x2 : -2 :  0 : x5 : xs)           = d (x0 : 2 : x2 : x5-2 : xs)
-- d (x0 :  2 : -3 : x3 :  0 : x5 : xs)           = (3, 0, x0 : 2 : -3 : (x3+x5) : xs)
-- d (x0 :  2 : -2 : -1 :  2 :  0 : x6 : xs)      = d (x0 : 2 : -2 : -1 : x6+2 : xs)
-- d (x0 :  2 : -2 : -1 : x4 :  0 : x6 : xs)      = (4, 0, x0 : 2 : -2 : -1 : (x4+x6) : xs)
-- d (x0 :  2 : -2 : -1 :  2 :  2 :  0 : x7 : xs) = d (x0 : 2 : -2 : -1 : 2 : x7+2 :  xs)
-- d (x0 :  2 : -2 : -1 : x4 : -2 :  0 : x7 : xs) = d (x0 : 2 : -2 : -1 : x4 : x7-2 :  xs)
-- d (x0 :  2 : -2 : -1 :  2 : -3 :  0 : x7 : xs) = d (x0 : 2 : -2 : -1 : 2 : x7-3 :  xs)

d xs@(_ : -2  : _) = (j, i, map negate xs')
  where (i, j, xs') = d $ map negate xs
d xs = (1, 1, xs)

bound :: CF' -> Interval
bound xs = Interval i s
  where (n, m, xs') = d xs
        Interval i _ = nthPrimitiveBounds xs' !! fromInteger n
        Interval _ s = nthPrimitiveBounds xs' !! fromInteger m

nextBound :: CF' -> Interval
nextBound xs = if a == 0 then
                 bound xs'
               else
                 go a xs'
  where (n, m, xs') = d xs
        a = min n m
        go 0 cs = bound cs
        go i (c:cs) = c .+ recips (go (i-1) cs)

sqrt2 :: CF
sqrt2 = CF $ 1 : repeat 2

exp1 :: CF
exp1 = CF $ 2 : concatMap triple [1..]
  where triple n = [1, 2 * n, 1]

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

  fromRational = CF . cfFromRational

digits :: CF' -> [Integer]
digits = go (1, 0, 0, 1)
  where go h cs = case intervalDigit $ boundHom h (bound cs) of
                       Nothing -> let (h', cs') = homAbsorb h cs in go h' cs'
                       Just d  -> d : go (homEmitDigit h d) cs
        base = 10
        homEmitDigit (n0, n1,
                      d0, d1) d = (base * (n0 - d0*d), base * (n1 - d1*d),
                                   d0,                 d1)

cfString :: CF -> String
cfString (CF cf) = case digits cf of
               [i] -> show i
               (i:is) -> show i ++ "." ++ concatMap show is

instance Show CF where
  show = take 50 . cfString
