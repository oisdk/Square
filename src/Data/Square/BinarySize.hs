module Data.Square.BinarySize where

import Data.Sequence.RightPerfect
import Data.Coerce.Utils
import Data.Functor.Identity
import Control.Applicative
import Data.Foldable

data Square xs a where
    Square :: (ArrayTraversable xs, ArrayIndex xs, ArrayZip xs)
           => Array xs (Array xs a) -> Square xs a

instance Foldable (Square xs) where
    foldMap f (Square xs) = arrayFoldMap (arrayFoldMap f) xs

instance Functor (Square xs) where
    fmap f (Square xs) = Square (arrayFmap (arrayFmap f) xs)

instance Traversable (Square xs) where
    traverse f (Square xs) = arrayTraverse Square (arrayTraverse id f) xs

create :: (KnownArray xs, ArrayCreate xs, Applicative f) => f a -> f (Square xs a)
create x = arrayCreate Square (arrayCreate id x)

instance (KnownArray xs, ArrayCreate xs) => Applicative (Square xs) where
    pure = runIdentity #. create .# Identity
    liftA2 f (Square xs) (Square ys) = Square (arrayZip (arrayZip f) xs ys)

index :: Applicative f => Int -> Int -> (a -> f a) -> Square xs a -> f (Square xs a)
index i j f (Square xs) = arrayIndex i Square (arrayIndex j id f) xs

transpose :: ArrayCreate xs => Square xs a -> Square xs a
transpose (Square xs) =
    Square
        (runWrappedArray (arrayTraverse id WrappedArray xs))

{-# ANN rows "HLint: ignore Use map" #-}
rows :: Square xs a -> [[a]]
rows (Square xs) = foldr (\y ys -> toList (WrappedArray y) : ys) [] (WrappedArray xs)

instance Show a => Show (Square xs a) where
    showsPrec n = showsPrec n . rows
