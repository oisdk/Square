{-# LANGUAGE TemplateHaskell #-}

module Main where

import           Control.Monad
import Control.Applicative
import           Data.Functor
import           Data.Ord
import           Data.Square
import           System.Exit
import           Test.QuickCheck
import qualified Test.QuickCheck.Property as P

toList :: Foldable f => f a -> [a]
toList = foldr (:) []

prop_correctSize :: Square Integer -> Bool
prop_correctSize s = n * n == length s where n = _squareSize s

prop_listIso :: NonEmptyList Integer -> Bool
prop_listIso (NonEmpty xs) = sameResult (Just . take m) (fmap toList . fromList n) xs where
  n = (floor . sqrt' . fromIntegral . length) xs
  m = n * n
  sqrt' :: Double -> Double
  sqrt' = sqrt

prop_listRev :: Square Integer -> Bool
prop_listRev s = sameResult Just (fromList n . toList) s where
  n = _squareSize s

prop_Indexing :: Square Integer -> Bool
prop_Indexing s = map (unsafeIndex s) ((,) <$> idxs <*> idxs) == toList s where
  idxs = [0..(_squareSize s - 1)]

prop_Ordering :: Square Integer -> Square Integer -> Property
prop_Ordering s t = classify (c==EQ) "Same size squares" . classify (c/=EQ) "Different sized squares" $
  case c of
    EQ -> r == comparing toList s t
    _  -> r == c
    where
      c = comparing _squareSize s t
      r = compare s t

sameResult :: Eq a => (b -> a) -> (b -> a) -> b -> Bool
sameResult = liftA2 (==)

sameResult2 :: Eq a => (c -> b -> a) -> (c -> b -> a) -> c -> b -> Bool
sameResult2 = liftA2 sameResult

quickCheckExit :: Testable prop => prop -> IO Result
quickCheckExit = resultExit <=< quickCheckResult where
  resultExit r@ Success{}  = pure r
  resultExit r = exitFailure $> r

failWith :: String -> P.Result
failWith r = P.failed { P.reason = r }

return []
runTests = $forAllProperties quickCheckExit

main = runTests
