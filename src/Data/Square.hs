{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Square where

import           Control.Applicative
import           Data.Coerce.Utils
import           Data.Sequence.RightPerfect
import qualified Data.Square.BinarySize     as Binary
import           Numeric.Binary

newtype Square n a = Square
    { runSquare :: Binary.Square (NatToBin n) a
    } deriving (Functor, Foldable, Traversable)

instance (KnownArray (NatToBin n), ArrayCreate (NatToBin n)) => Applicative (Square n) where
    pure = Square #. pure
    liftA2 f (Square xs) (Square ys) = Square (liftA2 f xs ys)

create
    :: forall n f a.
       (KnownArray (NatToBin n), ArrayCreate (NatToBin n), Applicative f)
    => f a -> f (Square n a)
create x = arrayCreate (Square #. Binary.Square) (arrayCreate id x)

index :: Applicative f => Int -> Int -> (a -> f a) -> Square xs a -> f (Square xs a)
index i j f (Square (Binary.Square xs)) =
    arrayIndex i (Square #. Binary.Square) (arrayIndex j id f) xs

transpose :: ArrayCreate (NatToBin n) => Square n a -> Square n a
transpose (Square (Binary.Square xs)) =
    Square (Binary.Square (runWrappedArray (arrayTraverse id WrappedArray xs)))

{-# ANN rows "HLint: ignore Use map" #-}
rows :: Square n a -> [[a]]
rows (Square xs) = Binary.rows xs

instance Show a => Show (Square n a) where
    showsPrec n = showsPrec n . rows
