{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main (main) where

import           Data.Square
import           Data.Square.Internal.Binary
import           Data.Type.Equality
import           Test.DocTest
import           Test.QuickCheck
import           Test.Semiring

instance (Creatable n, Arbitrary a) => Arbitrary (Square n a) where
  arbitrary = create arbitrary

instance Testable (Either String a) where
  property (Right _) = property True
  property (Left s)  = counterexample s False


type UnaryFun a  = a -> Either String String
type BinaryFun a  = a -> a -> Either String String
type TernaryFun a  = a -> a -> a -> Either String String

_toBinaryTests :: ()
_toBinaryTests = () where
  _one :: ToBinary 1 :~: 'I 'Z
  _one = Refl
  _zero :: ToBinary 0 :~: 'Z
  _zero = Refl
  _two :: ToBinary 2 :~: 'O ('I 'Z)
  _two = Refl
  _six :: ToBinary 6 :~: 'O ('I ('I 'Z))
  _six = Refl
  _sixHundred :: ToBinary 600 :~: 'O ('O ('O ('I ('I ('O ('I ('O ('O ('I 'Z)))))))))
  _sixHundred = Refl

main :: IO ()
main = do
    quickCheck (unaryLaws :: UnaryFun (Square 2 Integer))
    quickCheck (binaryLaws :: BinaryFun (Square 2 Integer))
    quickCheck (ternaryLaws :: TernaryFun (Square 2 Integer))
    quickCheck (unaryLaws :: UnaryFun (Square 3 Integer))
    quickCheck (binaryLaws :: BinaryFun (Square 3 Integer))
    quickCheck (ternaryLaws :: TernaryFun (Square 3 Integer))
    quickCheck (unaryLaws :: UnaryFun (Square 9 Integer))
    quickCheck (binaryLaws :: BinaryFun (Square 9 Integer))
    quickCheck (ternaryLaws :: TernaryFun (Square 9 Integer))
    doctest ["-isrc", "src/Data/Square.hs"]
