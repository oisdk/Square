{-# LANGUAGE TemplateHaskell #-}

module Main where

import           Control.Monad
import           Data.Functor
import           Data.Square
import           System.Exit
import           Test.QuickCheck
import qualified Test.QuickCheck.Property as P
import Data.Ord

toList :: Foldable f => f a -> [a]
toList = foldr (:) []

prop_correctSize :: Square Int -> Bool
prop_correctSize s = n * n == length s where n = _squareSize s

prop_listIso :: NonEmptyList Int -> Bool
prop_listIso (NonEmpty xs) = maybe False ((==) (take m xs) . toList) (fromList n xs) where
  n = (floor . sqrt' . fromIntegral . length) xs
  m = n * n
  sqrt' :: Double -> Double
  sqrt' = sqrt

prop_Indexing :: Square Int -> Bool
prop_Indexing s = [ unsafeIndex s (i,j) | i <- idxs, j <- idxs ] == toList s where
  idxs = [0..(_squareSize s - 1)]

prop_Ordering :: Square Int -> Square Int -> Property
prop_Ordering s t = classify (c==EQ) "Same size squares" . classify (c/=EQ) "Different sized squares" $
  case c of
    EQ -> r == comparing toList s t
    _  -> r == c
    where
      c = comparing _squareSize s t
      r = compare s t

quickCheckExit :: Testable prop => prop -> IO Result
quickCheckExit = resultExit <=< quickCheckResult where
  resultExit r@ Success{}  = pure r
  resultExit r = exitFailure $> r

failWith :: String -> P.Result
failWith r = P.failed { P.reason = r }

return []
runTests = $forAllProperties quickCheckExit

main = runTests
