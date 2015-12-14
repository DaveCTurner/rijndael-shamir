{-# LANGUAGE OverloadedStrings #-}

module Rijndael where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TBMQueue
import Control.Monad
import Data.Array.Unboxed
import Data.Maybe
import Data.Tuple
import Data.List
import Data.Bits
import Data.Word
import Math.Polynomial
import Math.Polynomial.Lagrange
import System.IO
import qualified Data.ByteString as B
import qualified Data.ByteString.Base16 as B16
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Test.QuickCheck
import Test.Hspec

import Debug.Trace

{-| The Rijndael field is a field of order 8, obtained as the quotient
    of the ring of polynomials with coefficients in the 2-element field {0,1}
    by the irreducible polynomial @X^8 + X^4 + X^3 + X + 1@. Elements are
    represented using Word8 indicating the polynomial coefficients

    0 -> 0
    1 -> 1
    2 -> X
    3 -> X + 1

    etc.  -}
newtype Rijndael = Rijndael { unRijndael :: Word8 } deriving (Show, Eq)

{- Every nonzero element in the Rijndael field is a power of (X+1), and (X+1)^255 == 1.
Thus powers of (X+1) can be computed with a lookup as follows. -}

pow3 :: Int -> Rijndael
pow3 n = Rijndael (pow3Table ! mod n 255)

pow3Table :: UArray Int Word8
pow3Table = listArray (0x00, 0xfe) $ iterate mul3 1
  where
  -- Multiply P by X ~ a<<1
  -- Therefore P(X+1) ~ xor a (a<<1) except a<<1 may overflow. If it does, note
  -- 0x100 ~= X^8 == X^4 + X^3 + X + 1 ~= 0b11011 == 0x1b so xor that too.
  mul3 a = foldr1 xor [a, shiftL a 1, if testBit a 7 then 0x1b else 0x00]

{- Conversely, logs base 3 as follows. -}

log3Table :: UArray Word8 Int
log3Table = array (0x01, 0xff) $ map swap $ assocs pow3Table

log3 :: Rijndael -> Int
log3 (Rijndael n) = log3Table ! n

{- Some algebraic properties. -}

prop_mul_0 :: Rijndael -> Bool
prop_mul_0 n = 0 * n == 0

prop_mul_1 :: Rijndael -> Bool
prop_mul_1 n = 1 * n == n

prop_mul_symm :: Rijndael -> Rijndael -> Bool
prop_mul_symm m n = m * n == n * m

prop_mul_assoc :: Rijndael -> Rijndael -> Rijndael -> Bool
prop_mul_assoc l m n = l * (m * n) == (l * m) * n

prop_mul_recip :: Rijndael -> Property
prop_mul_recip n = n /= 0 ==> n * recip n == 1

prop_mul_distrib :: Rijndael -> Rijndael -> Rijndael -> Bool
prop_mul_distrib l m n = l * (m + n) == (l * m) + (l * n)

prop_add_negate :: Rijndael -> Rijndael -> Bool
prop_add_negate m n = m - n == m + n

main = hspec $ describe "properties" $ do
  it "prop_mul_0"       $ property prop_mul_0
  it "prop_mul_1"       $ property prop_mul_1
  it "prop_mul_symm"    $ property prop_mul_symm
  it "prop_mul_assoc"   $ property prop_mul_assoc
  it "prop_mul_recip"   $ property prop_mul_recip
  it "prop_mul_distrib" $ property prop_mul_distrib
  it "prop_add_negate"  $ property prop_add_negate

instance Num Rijndael where
  (Rijndael x) + (Rijndael y) = Rijndael (x `xor` y)
  (Rijndael x) - (Rijndael y) = Rijndael (x `xor` y)
  x * y
    | x == 0 = 0
    | y == 0 = 0
    | otherwise = pow3 (log3 x + log3 y)
  negate = id
  fromInteger = Rijndael . fromInteger
  abs    _ = error "abs Rijndael"
  signum _ = error "signum Rijndael"

instance Fractional Rijndael where
  fromRational r = error "fromRational Rijndael"
  recip x = pow3 (255 - log3 x)

instance Arbitrary Rijndael where
  arbitrary = Rijndael <$> arbitrary

mainZ :: IO ()
mainZ = withFile "/dev/urandom" ReadMode $ \hRandom -> do
  let bytesToShare = T.encodeUtf8 "my secret text"
  let quorumSize = 3

  higherOrderCoefficients <- replicateM (quorumSize - 1) $ B.hGet hRandom $ B.length bytesToShare

  let result = share bytesToShare higherOrderCoefficients [0,1,2,3,4,5]

  mapM_ (print . B.unpack) result

{-| Reverse Shamir's secret sharing algorithm, revealing the shared secret. -}
unshare :: [(Word8, B.ByteString)] -> B.ByteString
unshare inputs = B.pack [ unRijndael $ lagrangeInterpolate wParts | wParts <- combinedParts ]
  where
  combinedParts :: [[(Rijndael, Rijndael)]]
  combinedParts = transpose $ map (\(w, bs) -> map ((,) (Rijndael w) . Rijndael) $ B.unpack bs) inputs

  {-| Given points on a polynomial 'xys', calculate the constant term (i.e. the value at X = 0)
  by the Lagrange interpolation formula. -}
  lagrangeInterpolate :: [(Rijndael, Rijndael)] -> Rijndael
  lagrangeInterpolate xys
      = sum [ yj * product [ xm / (xm - xj) | xm <- xsExceptJ ] | (xj, yj, xsExceptJ) <- terms xys ]
    where
    terms [] = []
    terms ((x,y):xys')
      = (x, y, map fst xys')
      : [(x', y', x : xs') | (x', y', xs') <- terms xys']

{-| Apply Shamir's secret sharing algorithm. -}
share :: B.ByteString -> [B.ByteString] -> [Word8] -> [B.ByteString]
share message higherOrderCoefficients xs = map (B.pack . map unRijndael) $ transpose outputs
  where
  polys :: [[Rijndael]]
  polys = map (map Rijndael) $ transpose $ map B.unpack $ message : higherOrderCoefficients

  evalPoly :: [Rijndael] -> [Rijndael]
  evalPoly coeffs = map (\x -> foldr (\c p -> c + p * Rijndael x) 0 coeffs) xs

  outputs :: [[Rijndael]]
  outputs = map evalPoly polys

addECC bs = B.pack $ map (unRijndael . evalPoly (sumPolys $ zipWith scalePoly vals basis) . Rijndael) [0..11]
  where
  vals = map Rijndael $ B.unpack bs
  basis = lagrangeBasis $ map Rijndael $ takeWhile (< fromIntegral (length vals)) [0..7]

addECCText = T.concat . concat . map (\(a,b) -> [a,b]) . zip (cycle ["  ", " "]) . T.chunksOf 4 . T.decodeUtf8 . B16.encode . addECC . fst . B16.decode . T.encodeUtf8 . T.filter (/= ' ')
