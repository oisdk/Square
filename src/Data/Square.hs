{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Square
  ( -- * The Square type
   Square
  ,KnownSquare
    -- * Creation
  ,fromList
  ,create
  ,replicate
  ,unfold
  ,unfoldMay
   -- * Modification
  ,alterF
   -- * Conversion
  ,rows
  ,cols
   -- * Indexing
  ,(!)
  ,row
  ,col)
  where

import Control.Applicative
import Data.Coerce
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Functor.Product
import Data.Monoid hiding (Product(..))
import Data.Proxy
import Data.Foldable hiding (traverse_)
import GHC.TypeLits
import Data.Semiring

import Data.Square.Binary

import Prelude hiding (replicate)

-- $setup
-- >>> :set -XDataKinds



-- | A square matrix. Adapted from
-- <http://www.usma.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp99square.pdf Okasaki's>
-- square matrices:
--
-- > data Square_ n v w a =
-- >    Zero (v (v a))
-- >  | Even (Square_          v    (Product w w) a)
-- >  | Odd  (Square_ (Product v w) (Product w w) a)
newtype Square n a =
  Square (Square_ (ToBinary n) Proxy Identity a)

data Base v a =
    Base (forall b. Int -> Traversal (v b) b)
         (v (v a))
    deriving (Functor,Foldable,Traversable)

type family Square_ n v w where
    Square_ 'Z v w = Base v
    Square_ ('O n) v w = Square_ n v (Product w w)
    Square_ ('I n) v w = Square_ n (Product v w) (Product w w)

type Traversal s a = ∀ f. Applicative f => (a -> f a) -> s -> f s

type KnownSquare n = KnownBinary (ToBinary n)

-- | Creates a square of side length @n@ from some applicative.
--
-- >>> create (Just 'a') :: Maybe (Square 1 Char)
-- Just ["a"]
create :: (Applicative f, KnownSquare n) => f a -> f (Square n a)
create = go Proxy
  where
    go
        :: (KnownSquare n, Applicative f)
        => Proxy n -> f a -> f (Square n a)
    go (_ :: Proxy n) =
        create_
            (Proxy :: Proxy (ToBinary n))
            Proxy
            Square
            leE
            leI
            0
            1
            (\k ->
                  (const . pure) (k Proxy))
            (fmap Identity)

instance KnownSquare n =>
         Functor (Square n) where
    fmap f (Square xs) =
        Square
            (fmap_
                 (Proxy :: Proxy (ToBinary n))
                 (Proxy :: Proxy Proxy)
                 (Proxy :: Proxy Identity)
                 f
                 xs)

instance KnownSquare n =>
         Foldable (Square n) where
    foldr f b (Square xs) =
        foldr_
            (Proxy :: Proxy (ToBinary n))
            (Proxy :: Proxy Proxy)
            (Proxy :: Proxy Identity)
            f
            b
            xs

instance KnownSquare n =>
         Traversable (Square n) where
    traverse f (Square xs) =
        Square <$>
        traverse_
            (Proxy :: Proxy (ToBinary n))
            (Proxy :: Proxy Proxy)
            (Proxy :: Proxy Identity)
            f
            xs

instance (Show a, KnownSquare n) => Show (Square n a) where
    showsPrec n = showsPrec n . rows

instance KnownSquare n => Eq1 (Square n) where
    liftEq eq xs ys = EQ == liftCompare (\x y -> if eq x y then EQ else LT) xs ys

instance KnownSquare n =>
         Ord1 (Square n) where
    liftCompare cmp (Square x) (Square y) =
        liftCompare_
            (Proxy :: Proxy (ToBinary n))
            (Proxy :: Proxy Proxy)
            (Proxy :: Proxy Identity)
            cmp
            x
            y

instance (KnownSquare n, Eq a) => Eq (Square n a) where
    (==) = liftEq (==)

instance (KnownSquare n, Ord a) => Ord (Square n a) where
    compare = liftCompare compare

instance KnownSquare n =>
         Applicative (Square n) where
    pure = replicate
    (<*>) = liftA2Sq ($)

liftA2Sq
    :: KnownSquare n
    => (a -> b -> c) -> Square n a -> Square n b -> Square n c
liftA2Sq f (Square xs :: Square n a) (Square ys) =
    Square
        (apply_
             (Proxy :: Proxy (ToBinary n))
             (Proxy :: Proxy Proxy)
             (Proxy :: Proxy Identity)
             f
             xs
             ys)

instance (KnownSquare n, Semiring a, KnownNat n) =>
         Semiring (Square n a) where
    zero = replicate zero
    one = unfold f 0
      where
        n = fromEnum (natVal (Proxy :: Proxy n))
        f 0 = (one, n)
        f m = (zero, m - 1)
    (<+>) = liftA2Sq (<+>)
    Square xs <.> Square ys =
        Square
            (mul_
                 (Proxy :: Proxy (ToBinary n))
                 (Proxy :: Proxy Proxy)
                 (Proxy :: Proxy Identity)
                 xs
                 ys)


rows :: KnownSquare n => Square n a -> [[a]]
rows (Square xs :: Square n a) =
    rows_
        (Proxy :: Proxy (ToBinary n))
        (Proxy :: Proxy Proxy)
        (Proxy :: Proxy Identity)
        xs

cols :: KnownSquare n => Square n a -> [[a]]
cols (Square xs :: Square n a) =
    cols_
        (Proxy :: Proxy (ToBinary n))
        (Proxy :: Proxy Proxy)
        (Proxy :: Proxy Identity)
        xs

mkP
  :: Applicative f
  => (Product v w a -> b) -> (f a -> f (v a)) -> (f a -> f (w a)) -> f a -> f b
mkP k = (liftA2.liftA2) (\x y -> k (Pair x y))

-- The indexing 'Traversal' for 'Proxy'. If this is called, it means an
-- invalid index has been given. This is caught earlier with the
-- 'Square' indexing functions.
leE :: Int -> Traversal (Proxy a) a
leE _ _ _ = pure Proxy

-- The indexing 'Traversal for 'Identity'.
leI :: Int -> Traversal (Identity a) a
leI 0 f (Identity x) = Identity <$> f x
leI _ _ i = pure i

-- The indexing 'Traversal for a pair
leP :: (Int -> Traversal (v a) a)
    -> (Int -> Traversal (w a) a)
    -> Int -> Int -> Traversal (Product v w a) a
leP lev lew nv i f (Pair v w)
  | i < nv    = flip Pair w <$> lev i f v
  | otherwise = Pair v <$> lew (i-nv) f w


class KnownBinary (n :: Binary)  where
    create_
        :: Applicative f
        => Proxy n
        -> Proxy w
        -> (Square_ n v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> f b -> f d)
        -> (forall b. f b -> f (w b))
        -> f a
        -> f c
    ix_
        :: Applicative f
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (Square_ n v w a -> b)
        -> Int
        -> Int
        -> (a -> f a)
        -> Square_ n v w a
        -> f b
    row_
        :: (Applicative f, Traversable v, Traversable w)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (Square_ n v w a -> b)
        -> Int
        -> (a -> f a)
        -> Square_ n v w a
        -> f b
    col_
        :: (Applicative f, Traversable v, Traversable w)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (Square_ n v w a -> b)
        -> Int
        -> (a -> f a)
        -> Square_ n v w a
        -> f b
    rows_
        :: (Foldable v, Foldable w)
        => Proxy n -> Proxy v -> Proxy w -> Square_ n v w a -> [[a]]
    cols_
        :: (Foldable v, Foldable w)
        => Proxy n -> Proxy v -> Proxy w -> Square_ n v w a -> [[a]]
    fmap_
        :: (Functor v, Functor w)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (a -> b)
        -> Square_ n v w a
        -> Square_ n v w b
    foldr_
        :: (Foldable v, Foldable w)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (a -> b -> b)
        -> b
        -> Square_ n v w a
        -> b
    traverse_
        :: (Traversable v, Traversable w, Applicative f)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (a -> f b)
        -> Square_ n v w a
        -> f (Square_ n v w b)
    liftCompare_
        :: (Ord1 v, Ord1 w)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (a -> b -> Ordering)
        -> Square_ n v w a
        -> Square_ n v w b
        -> Ordering
    apply_
        :: (Applicative v, Applicative w)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> (a -> b -> c)
        -> Square_ n v w a
        -> Square_ n v w b
        -> Square_ n v w c
    mul_
        :: (Applicative v
           ,Applicative w
           ,Traversable v
           ,Traversable w
           ,Semiring a)
        => Proxy n
        -> Proxy v
        -> Proxy w
        -> Square_ n v w a
        -> Square_ n v w a
        -> Square_ n v w a

instance KnownBinary 'Z where
    create_ _ _ k lev _ _ _ mkv _ = mkv (k . Base lev) . mkv id
    ix_ _ _ _ k i j f (Base lev xs) = k . Base lev <$> (lev i . lev j) f xs
    row_ _ _ _ k i f (Base lev vv) =
        fmap (k . Base lev) ((lev i . traverse) f vv)
    col_ _ _ _ k i f (Base lev vv) =
        fmap (k . Base lev) ((traverse . lev i) f vv)
    rows_ _ _ _ (Base _ xs) = foldr ((:) . toList) [] xs
    cols_ _ _ _ (Base _ xs) = foldr (foldr f (const [])) (repeat []) xs
      where
        f e a (y:ys) = (e : y) : a ys
        f _ _ [] = []
    fmap_ _ _ _ f (Base lev xs) = Base lev ((fmap.fmap) f xs)
    foldr_ _ _ _ f b (Base _ xs) = foldr (flip (foldr f)) b xs
    traverse_ _ _ _ f (Base lev xs) = Base lev <$> (traverse.traverse) f xs
    liftCompare_ _ _ _ cmp (Base _ xs) (Base _ ys) = liftCompare (liftCompare cmp) xs ys
    apply_ _ _ _ f (Base lev xs) (Base _ ys) = Base lev (liftA2 (liftA2 f) xs ys)
    mul_ _ _ _ (Base lev xs) (Base _ ys) = Base lev (getMatrix (Matrix xs <.> Matrix ys))
    {-# INLINE create_ #-}
    {-# INLINE ix_ #-}
    {-# INLINE row_ #-}
    {-# INLINE col_ #-}
    {-# INLINE rows_ #-}
    {-# INLINE cols_ #-}
    {-# INLINE fmap_ #-}
    {-# INLINE foldr_ #-}
    {-# INLINE traverse_ #-}
    {-# INLINE liftCompare_ #-}
    {-# INLINE apply_ #-}
    {-# INLINE mul_ #-}

instance KnownBinary n =>
         KnownBinary ('O n) where
    create_ _ (_ :: Proxy w) k lev lew vsz wsz mkv mkw =
        create_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product w w))
            k
            lev
            (leP lew lew wsz)
            vsz
            (wsz + wsz)
            mkv
            (mkP id mkw mkw)
    ix_ _ (_ :: Proxy v) (_ :: Proxy w) =
        ix_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    row_ _ (_ :: Proxy v) (_ :: Proxy w) =
        row_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    col_ _ (_ :: Proxy v) (_ :: Proxy w) =
        col_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    rows_ _ (_ :: Proxy v) (_ :: Proxy w) =
        rows_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    cols_ _ (_ :: Proxy v) (_ :: Proxy w) =
        cols_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    fmap_ _ (_ :: Proxy v) (_ :: Proxy w) =
        fmap_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    foldr_ _ (_ :: Proxy v) (_ :: Proxy w) =
        foldr_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    traverse_ _ (_ :: Proxy v) (_ :: Proxy w) =
        traverse_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    liftCompare_ _ (_ :: Proxy v) (_ :: Proxy w) =
        liftCompare_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    apply_ _ (_ :: Proxy v) (_ :: Proxy w) =
        apply_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    mul_ _ (_ :: Proxy v) (_ :: Proxy w) =
        mul_
            (Proxy :: Proxy n)
            (Proxy :: Proxy v)
            (Proxy :: Proxy (Product w w))
    {-# INLINE create_ #-}
    {-# INLINE ix_ #-}
    {-# INLINE row_ #-}
    {-# INLINE col_ #-}
    {-# INLINE rows_ #-}
    {-# INLINE cols_ #-}
    {-# INLINE fmap_ #-}
    {-# INLINE foldr_ #-}
    {-# INLINE traverse_ #-}
    {-# INLINE liftCompare_ #-}
    {-# INLINE apply_ #-}
    {-# INLINE mul_ #-}

instance KnownBinary n =>
         KnownBinary ('I n) where
    create_ _ _ k lev lew vsz wsz mkv mkw =
        create_
            (Proxy :: Proxy n)
            Proxy
            k
            (leP lev lew vsz)
            (leP lew lew wsz)
            (vsz + wsz)
            (wsz + wsz)
            (\c ->
                  mkP c (mkv id) mkw)
            (mkP id mkw mkw)
    ix_ _ (_ :: Proxy v) (_ :: Proxy w) =
        ix_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    row_ _ (_ :: Proxy v) (_ :: Proxy w) =
        row_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    col_ _ (_ :: Proxy v) (_ :: Proxy w) =
        col_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    rows_ _ (_ :: Proxy v) (_ :: Proxy w) =
        rows_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    cols_ _ (_ :: Proxy v) (_ :: Proxy w) =
        cols_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    fmap_ _ (_ :: Proxy v) (_ :: Proxy w) =
        fmap_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    foldr_ _ (_ :: Proxy v) (_ :: Proxy w) =
        foldr_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    traverse_ _ (_ :: Proxy v) (_ :: Proxy w) =
        traverse_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    liftCompare_ _ (_ :: Proxy v) (_ :: Proxy w) =
        liftCompare_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    apply_ _ (_ :: Proxy v) (_ :: Proxy w) =
        apply_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    mul_ _ (_ :: Proxy v) (_ :: Proxy w) =
        mul_
            (Proxy :: Proxy n)
            (Proxy :: Proxy (Product v w))
            (Proxy :: Proxy (Product w w))
    {-# INLINE create_ #-}
    {-# INLINE ix_ #-}
    {-# INLINE row_ #-}
    {-# INLINE col_ #-}
    {-# INLINE rows_ #-}
    {-# INLINE cols_ #-}
    {-# INLINE fmap_ #-}
    {-# INLINE foldr_ #-}
    {-# INLINE traverse_ #-}
    {-# INLINE liftCompare_ #-}
    {-# INLINE apply_ #-}
    {-# INLINE mul_ #-}



-- ------------------------------------------------------------------------
-- -- Indexing
-- ------------------------------------------------------------------------

alterF
    :: (Applicative f, KnownNat n, KnownSquare n)
    => (a -> f a) -> (Int, Int) -> Square n a -> f (Square n a)
alterF f (i,j) s@(Square q :: Square n a)
  | i < 0 = pure s
  | j < 0 = pure s
  | i >= n = pure s
  | j >= n = pure s
  | otherwise =
      ix_
          (Proxy :: Proxy (ToBinary n))
          (Proxy :: Proxy Proxy)
          (Proxy :: Proxy Identity)
          Square
          i
          j
          f
          q
  where
    n = fromInteger (natVal (Proxy :: Proxy n))

(!) :: (KnownSquare n, KnownNat n) => Square n a -> (Int, Int) -> Maybe a
s ! i = (getFirst .# getConst) ((`alterF` i) (Const .# First .# Just) s)

infixr 9 .#
(.#) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(.#) _ = coerce

row :: (KnownSquare n) => Int -> Traversal (Square n a) a
row i f (Square xs :: Square n a) =
    row_
        (Proxy :: Proxy (ToBinary n))
        (Proxy :: Proxy Proxy)
        (Proxy :: Proxy Identity)
        Square
        i
        f
        xs

col :: (KnownSquare n) => Int -> Traversal (Square n a) a
col i f (Square xs :: Square n a) =
    col_
        (Proxy :: Proxy (ToBinary n))
        (Proxy :: Proxy Proxy)
        (Proxy :: Proxy Identity)
        Square
        i
        f
        xs

-- ------------------------------------------------------------------------
-- -- fromList
-- ------------------------------------------------------------------------

newtype State s a = State (s -> (a, s))

instance Functor (State s) where
    fmap f (State r) =
        State (\s -> case r s of (x,s') -> s' `seq` (f x, s'))
    {-# INLINABLE fmap #-}

instance Applicative (State s) where
    pure x = State (\s -> (x, s))
    {-# INLINABLE pure #-}
    State fs <*> State xs = State (\s -> case fs s of
                                      (f, s') -> case xs s' of
                                        (x, s'') -> s'' `seq` (f x, s''))
    {-# INLINABLE (<*>) #-}

evalState :: State s a -> s -> a
evalState (State r) s = case r s of
  (x, _) -> x

newtype MaybeState s a = MaybeState (s -> Maybe (a, s))

instance Functor (MaybeState s) where
    fmap f (MaybeState r) =
        MaybeState
            (\s ->
                  case r s of
                      Just (x,s') -> s' `seq` Just (f x, s')
                      Nothing -> Nothing)
    {-# INLINABLE fmap #-}

instance Applicative (MaybeState s) where
    pure x = MaybeState (\s -> Just (x, s))
    MaybeState fs <*> MaybeState xs =
        MaybeState
            (\s ->
                  case fs s of
                      Nothing -> Nothing
                      Just (f,s') ->
                          case xs s' of
                              Nothing -> Nothing
                              Just (x,s'') -> s'' `seq` Just (f x, s''))

evalMaybeState :: MaybeState s a -> s -> Maybe a
evalMaybeState (MaybeState r) s = case r s of
  Nothing -> Nothing
  Just (x,_) -> Just x

fromList :: KnownSquare n => [a] -> Maybe (Square n a)
fromList = unfoldMay uncons' where
  uncons' [] = Nothing
  uncons' (x:xs) = Just (x,xs)

replicate :: KnownSquare n => a -> Square n a
replicate x = runIdentity (create (Identity x))

unfold :: KnownSquare n => (b -> (a, b)) -> b -> Square n a
unfold f = evalState (create (State f))

unfoldMay :: KnownSquare n => (b -> Maybe (a, b)) -> b -> Maybe (Square n a)
unfoldMay f = evalMaybeState (create (MaybeState f))
