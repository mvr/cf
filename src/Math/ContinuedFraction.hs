module Math.ContinuedFraction
  (
    CF,
    convergents,
    digits,
    showCF
  ) where

import Data.Ratio

newtype CF = CF [Integer]

-- | Produce a list of rational approximations to a number
convergents :: CF -> [Rational]
convergents (CF cf) = go 0 1 1 0 cf
  where go p q p' q' (a:as) = (newp % newq) : go p' q' newp newq as
          where newp = a * p' + p
                newq = a * q' + q
        go _ _ _ _ [] = []

-- | Produce a list of digits in a given base
digits :: Integer -> CF -> [Integer]
digits base (CF cf) = go 0 1 1 0 cf
  where go 0 _ 0 _ _        = []
        go _ _ p' q' []     = go p' q' p' q' [0]
        go p q p' q' (a:as) = case digit p q p' q' of
                                Just d -> d : go (base * (p - d * q)) q (base * (p' - d * q')) q' (a:as)
                                Nothing -> go p' q' (a * p' + p) (a * q' + q) as
        digit p q p' q' = if q' /= 0 && q /= 0 && p `quot` q == p' `quot` q' then
                            Just $ p `quot` q
                          else
                            Nothing

-- | Produce a decimal representation of a number
showCF :: CF -> String
showCF cf | cf < 0 = "-" ++ show (-cf)
showCF (CF [i])   = show i
showCF (CF (i:r)) = show i ++ "." ++ decimalDigits
  where decimalDigits = concatMap show $ tail $ digits 10 (CF (0:r))

instance Show CF where
  show = take 15 . showCF

safeHead :: [a] -> Maybe a
safeHead (x:_) = Just x
safeHead [] = Nothing

safeRest :: [a] -> [a]
safeRest (_:xs) = xs
safeRest [] = []

-- The coefficients of the homographic function (a + bx) / (c+dx)
type Hom = (Integer, Integer,
            Integer, Integer)

-- Possibly output a term and return the simplified hom
emit :: Hom -> Maybe (Hom, Integer)
emit (a, b,
      c, d) = if c /= 0 && d /= 0 && r == s then
                Just ((c,       d,
                       a - c*r, b-d*r), r)
              else
                Nothing
  where r = a `quot` c
        s = b `quot` d

-- Absorb the next term
ingest :: Hom -> Maybe Integer -> Hom
ingest (a, b,
        c, d) (Just p) = (b, a+b*p,
                          d, c+d*p)
ingest (_a, b,
        _c, d) Nothing  = (b, b,
                           d, d)

-- Apply a hom to a continued fraction
hom :: Hom -> [Integer] -> [Integer]
hom (0, 0,
     _, _) _ = [0]
hom (_, _,
     0, 0) _ = []
hom h x = case emit h of
           Just (next, d) -> d : hom next x
           Nothing -> hom (ingest h (safeHead x)) (safeRest x)

-- The coefficients of the bihomographic function (a + bx + cy + dxy) / (e + fx + gy + hxy)
type Bihom = (Integer, Integer, Integer, Integer,
              Integer, Integer, Integer, Integer)

-- Possibly output a term and return the simplified bihom
biemit :: Bihom -> Maybe (Bihom, Integer)
biemit (a, b, c, d,
        e, f, g, h) = if e /= 0 && f /= 0 && g /= 0 && h /= 0 && ratiosAgree then
                      Just ((e,     f,     g,     h ,
                             a-e*r, b-f*r, c-g*r, d-h*r), r)
                    else
                      Nothing
  where r = a `quot` e
        ratiosAgree = r == (b `quot` f) && r == (c `quot` g) && r == (d `quot` h)

-- Absorb a term from x
ingestX :: Bihom -> Maybe Integer -> Bihom
ingestX (a, b, c, d,
         e, f, g, h) (Just p)  = (b, a+b*p, d, c+d*p,
                                  f, e+f*p, h, g+h*p)
ingestX (_a, b, _c, d,
         _e, f, _g, h) Nothing = (b, b, d, d,
                                  f, f, h, h)
-- Absorb a term from y
ingestY :: Bihom -> Maybe Integer -> Bihom
ingestY (a, b, c, d,
         e, f, g, h) (Just q)  = (c, d, a+c*q, b+d*q,
                                  g, h, e+g*q, f+h*q)
ingestY (_a, _b, c, d,
         _e, _f, g, h) Nothing = (c, d, c, d,
                                  g, h, g, h)

-- Decide which of x and y to pull a term from
shouldIngestX :: Bihom -> Bool
shouldIngestX (_, _, _, _,
               0, 0, _, _) = False
shouldIngestX (_, _, _, _,
               0, _, 0, _) = True
shouldIngestX (a, b, c, _,
               e, f, g, _) = abs (g*e*b - g*a*f) > abs (f*e*c - g*a*f)

-- Apply a bihom to two continued fractions
bihom :: Bihom -> [Integer] -> [Integer] -> [Integer]
bihom (_, _, _, _,
       0, 0, 0, 0) _ _ = []
bihom (0, 0, 0, 0,
       _, _, _, _) _ _ = [0]
bihom bh x y = case biemit bh of
                Just (next, d) -> d : bihom next x y
                Nothing -> if shouldIngestX bh then
                             bihom (ingestX bh (safeHead x)) (safeRest x) y
                           else
                             bihom (ingestY bh (safeHead y)) x (safeRest y)

instance Eq CF where
  x == y = compare x y == EQ

instance Ord CF where
  -- As [..., n, 1] represents the same number as [..., n+1]
  compare (CF [x]) (CF [y, 1]) = compare x (y+1)
  compare (CF [x, 1]) (CF [y]) = compare (x+1) y
  compare (CF [x]) (CF [y]) = compare x y

  compare (CF (x:_)) (CF [y]) = if x < y then LT else GT
  compare (CF [x]) (CF (y:_)) = if x > y then GT else LT

  compare (CF (x:xs)) (CF (y:ys)) = case compare x y of
                                     EQ -> opposite $ compare (CF xs) (CF ys)
                                     o  -> o
    where opposite LT = GT
          opposite EQ = EQ
          opposite GT = LT

instance Num CF where
  (CF x) + (CF y) = CF (bihom (0, 1, 1, 0,
                               1, 0, 0, 0) x y)
  (CF x) * (CF y) = CF (bihom (0, 0, 0, 1,
                               1, 0, 0, 0) x y)
  (CF x) - (CF y) = CF (bihom (0, 1, -1, 0,
                               1, 0,  0, 0) x y)
  fromInteger i = CF [i]
  abs x = if x > 0 then
             x
          else
            -x
  signum x | x < 0  = -1
           | x == 0 = 0
           | x > 0 = 1

instance Enum CF where
  toEnum = fromInteger . fromIntegral
  fromEnum = floor

instance Fractional CF where
  (CF x) / (CF y) = CF (bihom (0, 1, 0, 0,
                               0, 0, 1, 0) x y)

  recip (CF [1]) = CF [1]
  recip (CF (0:xs)) = CF xs
  recip (CF xs) = CF (0:xs)

  fromRational r = fromInteger n / fromInteger d
    where n = numerator r
          d = denominator r

instance Real CF where
  -- Just take a pretty good rational approximation
  toRational cf = last $ take 20 (convergents cf)

instance RealFrac CF where
  properFraction (CF [i]) = (fromIntegral i, 0)
  properFraction cf | cf < 0 = case properFraction (-cf) of
                                (b, a) -> (-b, -a)
  properFraction (CF (i:r)) = (fromIntegral i, CF r)

-- instance Floating CF where
--   pi = undefined
--   exp = undefined
--   log = undefined
--   sin = undefined
--   cos = undefined
--   asin = undefined
--   atan = undefined
--   acos = undefined
--   sinh = undefined
--   cosh = undefined
--   asinh = undefined
--   atanh = undefined
--   acosh = undefined
