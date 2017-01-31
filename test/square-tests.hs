{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DataKinds #-}

module Main (main) where

import           Data.Square
import           Test.DocTest
import           Test.QuickCheck
import Test.Semiring

instance (Creatable n, Arbitrary a) => Arbitrary (Square n a) where
  arbitrary = create arbitrary

instance Testable (Either String a) where
  property (Right _) = property True
  property (Left s) = counterexample s False


type Unary a  = a -> Either String String
type Binary a  = a -> a -> Either String String
type Ternary a  = a -> a -> a -> Either String String

main :: IO ()
main = do
    quickCheck (unaryLaws   :: Unary   (Square 2 Integer))
    quickCheck (binaryLaws  :: Binary  (Square 2 Integer))
    quickCheck (ternaryLaws :: Ternary (Square 2 Integer))
    quickCheck (unaryLaws   :: Unary   (Square 3 Integer))
    quickCheck (binaryLaws  :: Binary  (Square 3 Integer))
    quickCheck (ternaryLaws :: Ternary (Square 3 Integer))
    quickCheck (unaryLaws   :: Unary   (Square 9 Integer))
    quickCheck (binaryLaws  :: Binary  (Square 9 Integer))
    quickCheck (ternaryLaws :: Ternary (Square 9 Integer))
    doctest ["-isrc", "src/Data/Square.hs"]
