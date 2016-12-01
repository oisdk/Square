{-# LANGUAGE TypeApplications #-}

module Main (main) where

import           Data.Foldable
import           Data.Ix
import           Data.Maybe      (catMaybes)
import           Data.Square
import           Test.DocTest
import           Test.QuickCheck

squares :: Arbitrary a => Gen (Square a)
squares = sized (`create` arbitrary)

intSquares :: Gen (Square Integer)
intSquares = squares

selfEqualsSelf :: (Show a, Eq a) => a -> Property
selfEqualsSelf s = s === s

fromListToListIsId :: (Eq a, Show a) => [a] -> Property
fromListToListIsId xs =
  let n = (floor.sqrt.fromIntegral.length) xs
      Just s = fromList n xs
  in toList s === take (n*n) xs

indexingIsConsistent :: (Eq a, Show a) => Square a -> Property
indexingIsConsistent s =
  toList s ===
  catMaybes [ s ! (i,j)
            | (i,j) <- range ((0,0),(squareSize s - 1, squareSize s - 1))]

main :: IO ()
main = do
  quickCheck (forAll intSquares selfEqualsSelf)
  quickCheck (fromListToListIsId :: [Integer] -> Property)
  quickCheck (forAll intSquares indexingIsConsistent)
  doctest [ "-isrc"
          , "src/Data/Square.hs" ]
