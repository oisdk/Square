{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}

module Data.Sequence.RightPerfect where

import Numeric.Peano
import Data.Kind
import Control.Applicative
import Data.Bits
import Data.Functor.Identity
import Data.Traversable
import Data.Coerce.Utils

{-# ANN module "HLint: ignore Avoid lambda" #-}

data Nil a = Nil

type family Array (xs :: [ℕ]) = (arr :: Type -> Type) | arr -> xs where
    Array '[]        = Nil
    Array (Z   : xs) = Odd xs
    Array (S x : xs) = Even x xs

data Odd  xs a   = Odd a (Array xs a) (Array xs a)
data Even x xs a = Even (Array (x:xs) a) (Array (x:xs) a)

class ArrayTraversable xs where
    arrayTraverse :: Applicative f => (Array xs b -> c) -> (a -> f b) -> Array xs a -> f c

instance ArrayTraversable '[] where
    arrayTraverse k _ _ = pure (k Nil)

instance ArrayTraversable xs =>
         ArrayTraversable ('Z : xs) where
    arrayTraverse k f (Odd x ys zs) =
        liftA3
            (\x' ys' zs' ->
                  k (Odd x' ys' zs'))
            (f x)
            (arrayTraverse id f ys)
            (arrayTraverse id f zs)

instance ArrayTraversable (x : xs) =>
         ArrayTraversable ('S x : xs) where
    arrayTraverse k f (Even xs ys) =
        liftA2
            (\xs' ys' ->
                  k (Even xs' ys'))
            (arrayTraverse id f xs)
            (arrayTraverse id f ys)

class ArrayCreate xs where
    arrayCreate :: Applicative f => (Array xs a -> b) -> f a -> f b

instance ArrayCreate '[] where
    arrayCreate k _ = pure (k Nil)

instance ArrayCreate xs => ArrayCreate ('Z : xs) where
    arrayCreate k x = let ys = arrayCreate id x in liftA3 (\x' ys' zs' -> k (Odd x' ys' zs')) x ys ys

instance ArrayCreate (x:xs) => ArrayCreate ('S x : xs) where
    arrayCreate k x = let ys = arrayCreate id x in liftA2 (\ ys' zs' → k (Even ys' zs')) ys ys

class ArrayZip xs where
    arrayZip :: (a -> b -> c) -> Array xs a -> Array xs b -> Array xs c

instance ArrayZip '[] where
    arrayZip _ _ _ = Nil

instance ArrayZip xs => ArrayZip ('Z:xs) where
    arrayZip f (Odd x1 ys1 zs1) (Odd x2 ys2 zs2)
        = Odd (f x1 x2) (arrayZip f ys1 ys2) (arrayZip f zs1 zs2)

instance ArrayZip (x:xs) => ArrayZip ('S x : xs) where
    arrayZip f (Even xs1 ys1) (Even xs2 ys2) = Even (arrayZip f xs1 xs2) (arrayZip f ys1 ys2)

class ArrayIndex (xs :: [ℕ]) where
    arrayIndex :: Applicative f => Int -> (Array xs a -> b) -> (a -> f a) -> Array xs a -> f b

instance ArrayIndex '[] where
    arrayIndex _ k _ _ = pure (k Nil)

instance ArrayIndex xs => ArrayIndex ('Z:xs) where
    arrayIndex 0 k f (Odd x ys zs) = fmap (\x' -> k (Odd x' ys zs)) (f x)
    arrayIndex i k f (Odd x ys zs) = case i - 1 of
        !j -> if testBit j 0
              then arrayIndex (shiftR j 1) (\zs' -> k (Odd x ys zs')) f zs
              else arrayIndex (shiftR j 1) (\ys' -> k (Odd x ys' zs)) f ys

instance ArrayIndex (x:xs) => ArrayIndex ('S x : xs) where
    arrayIndex i k f (Even xs ys)
      | testBit i 0 = arrayIndex (shiftR i 1) (\ys' -> k (Even xs  ys')) f ys
      | otherwise   = arrayIndex (shiftR i 1) (\xs' -> k (Even xs' ys)) f xs

arrayFoldMap :: forall xs a b. (ArrayTraversable xs, Monoid b) => (a -> b) -> Array xs a -> b
arrayFoldMap f = getConst #. arrayTraverse id (Const #. f)
{-# INLINE arrayFoldMap #-}

arrayFmap :: forall xs a b. (ArrayTraversable xs) => (a -> b) -> Array xs a -> Array xs b
arrayFmap f = runIdentity #. arrayTraverse id (Identity #. f)
{-# INLINE arrayFmap #-}

type KnownArray xs = (ArrayTraversable xs, ArrayIndex xs, ArrayZip xs)

newtype WrappedArray xs a
    = WrappedArray { runWrappedArray :: Array xs a }

instance ArrayTraversable xs => Functor (WrappedArray xs) where
    fmap = fmapDefault

instance ArrayTraversable xs => Foldable (WrappedArray xs) where
    foldMap = foldMapDefault

instance ArrayTraversable xs => Traversable (WrappedArray xs) where
    traverse f (WrappedArray xs) = arrayTraverse WrappedArray f xs

instance (ArrayCreate xs, ArrayZip xs, ArrayTraversable xs) =>
         Applicative (WrappedArray xs) where
    pure = WrappedArray #. runIdentity #. arrayCreate id .# Identity
    liftA2 f (WrappedArray xs) (WrappedArray ys) = WrappedArray (arrayZip f xs ys)
