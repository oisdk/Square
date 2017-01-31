{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Square
  (Square
  ,rows
  ,cols
  ,fromList
  ,create
  ,alterF
  ,(!))
  where

import Control.Applicative
import Data.Coerce
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Functor.Product
import Data.Monoid hiding (Product(..))
import Data.Proxy
import Data.Foldable
import Data.Semiring
import GHC.TypeLits

data Binary = Z | O Binary | I Binary

type family Even (n :: Nat) (true :: k) (false :: k) :: k where
  Even 0 true false = true
  Even 1 true false = false
  Even n true false = Even (n-2) true false

type family Half (n :: Nat) :: Nat where
  Half 0 = 0
  Half 1 = 0
  Half n = Half (n-2) + 1

type family ToBinary (n :: Nat) :: Binary where
  ToBinary 0 = 'Z
  ToBinary n = (Even n 'O 'I) (ToBinary (Half n))

-- | This type represents a square matrix. In the form:
--
-- > Square_ Proxy Identity a
--
-- It is unable to be a non-square. It is adapted from
-- <http://www.usma.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp99square.pdf Okasaki's>
-- square matrices:
--
-- > data Square_ n v w a =
-- >    Zero (v (v a))
-- >  | Even (Square_      v     (Product w w) a)
-- >  | Odd  (Square_ (Product v w) (Product w w) a)
--
-- The extra field in the @Zero@ branch is a function which, when
-- given a valid index, produces a Lens into the element at that
-- position. This could be accomplished without the field, but this
-- way allows sharing of work across repeated access to different
-- indices.
newtype Square n a =
  Square { getSquare :: Square_ (ToBinary n) Proxy Identity a
         } deriving (Functor, Foldable, Traversable, Eq, Ord, Eq1, Ord1)

type Lens s a = ∀ f. Functor f => (a -> f a) -> s -> f s

data Square_ n v w a where
  Zero :: (∀ b. Int -> Lens (v b) b) -> v (v a) -> Square_ 'Z v w a
  Even :: Square_ n          v    (Product w w) a   -> Square_ ('O n) v w a
  Odd  :: Square_ n (Product v w) (Product w w) a   -> Square_ ('I n) v w a

deriving instance (Functor v, Functor w) => Functor (Square_ n v w)
deriving instance (Foldable v, Foldable w) => Foldable (Square_ n v w)
deriving instance (Traversable v, Traversable w) => Traversable (Square_ n v w)

newtype FreeMonoid a = FreeMonoid { runFree :: ∀ b. Monoid b => (a -> b) -> b }

instance Monoid (FreeMonoid a) where
  mempty = FreeMonoid (const mempty)
  {-# INLINE mempty #-}
  mappend (FreeMonoid x) (FreeMonoid y) = FreeMonoid (\f -> x f <> y f)
  {-# INLINE mappend #-}

instance Functor FreeMonoid where
  fmap f (FreeMonoid fld) = FreeMonoid (\g -> fld (g . f))
  {-# INLINE fmap #-}

newtype Sequence f a = Sequence { unSequence :: f a } deriving (Functor, Applicative)

instance (Applicative f, Monoid a) =>
         Monoid (Sequence f a) where
    mempty = Sequence (pure mempty)
    {-# INLINE mempty #-}
    mappend =
        (coerce :: (f a -> f a -> f a) -> Sequence f a -> Sequence f a -> Sequence f a)
            (liftA2 mappend)
    {-# INLINE mappend #-}

instance Applicative FreeMonoid where
    pure x = FreeMonoid ($x)
    FreeMonoid fs <*> FreeMonoid xs =
        FreeMonoid
            (\k ->
                  fs
                      (\c ->
                            xs (k . c)))

instance Foldable FreeMonoid where foldMap = flip runFree

instance Traversable FreeMonoid where
  traverse f (FreeMonoid xs) = (unSequence .# xs) (Sequence .# fmap pure . f)
  {-# INLINE traverse #-}

instance Show a => Show (FreeMonoid a) where
  showsPrec n = showsPrec n . toList

toFreeMonoid :: Foldable f => f a -> FreeMonoid a
toFreeMonoid xs = FreeMonoid (`foldMap` xs)

class Monoid1 f  where
    liftMappend :: a -> (a -> a -> a) -> f a -> f a -> f a
    liftEmpty :: a -> f a

instance Monoid1 Identity where
    liftMappend _ = coerce
    liftEmpty = coerce
    {-# INLINE liftMappend #-}
    {-# INLINE liftEmpty #-}

instance Monoid1 Proxy where
    liftMappend _ _ _ _ = Proxy
    liftEmpty _ = Proxy
    {-# INLINE liftMappend #-}
    {-# INLINE liftEmpty #-}

instance (Monoid1 w, Monoid1 v) =>
         Monoid1 (Product w v) where
    liftMappend empt mapp (Pair w x) (Pair y z) =
        Pair (liftMappend empt mapp w y) (liftMappend empt mapp x z)
    liftEmpty e = Pair (liftEmpty e) (liftEmpty e)
    {-# INLINE liftMappend #-}
    {-# INLINE liftEmpty #-}

mappend1 :: (Monoid1 f, Monoid a) => f a -> f a -> f a
mappend1 = liftMappend mempty mappend
{-# INLINE mappend1 #-}

empty1 :: (Monoid1 f, Monoid a) => f a
empty1 = liftEmpty mempty
{-# INLINE empty1 #-}

rows :: Square n a -> FreeMonoid (FreeMonoid a)
rows = go toFreeMonoid . getSquare
  where
    go
        :: (Foldable w, Foldable v, Functor v, Functor w)
        => (v a -> FreeMonoid a) -> Square_ n v w a -> FreeMonoid (FreeMonoid a)
    go f (Zero _ x) = toFreeMonoid (fmap f x)
    go f (Even s) = go f s
    go f (Odd s) = go g s
      where
        g (Pair vs ws) = f vs <> toFreeMonoid ws

cols :: Square n a -> FreeMonoid (FreeMonoid a)
cols = go . getSquare
  where
    go
        :: (Foldable v, Foldable w, Functor v, Functor w, Monoid1 v, Monoid1 w)
        => Square_ n v w a -> FreeMonoid (FreeMonoid a)
    go (Zero _ x) = toFreeMonoid (foldr (mappend1 . fmap pure) empty1 x)
    go (Even s) = go s
    go (Odd s) = go s

mulM
    :: Semiring a
    => Square n a -> Square n a -> FreeMonoid (FreeMonoid a)
mulM x y = fmap (f . toList) (rows x)
  where
    f r = fmap (g r . toList) c
    c = cols y
    g rs cs = add (zipWith (<.>) rs cs)

mulMat
    :: (Semiring a, Create (ToBinary n))
    => Square n a -> Square n a -> Square n a
mulMat x y =
    let Just res = (fromList . toList . fold)  (mulM x y)
    in res

combAdd :: (Monoid1 v, Semiring a) => v a -> v a -> v a
combAdd = liftMappend zero (<+>)
{-# INLINE combAdd #-}

addMat :: (Semiring a) => Square n a -> Square n a -> Square n a
addMat (Square x) (Square y) = Square (go x y)
  where
    go
        :: (Functor v, Monoid1 v, Semiring a, Functor w, Monoid1 w)
        => Square_ n v w a -> Square_ n v w a -> Square_ n v w a
    go (Zero _ vx) (Zero ly vy) =
        Zero ly (liftMappend (liftEmpty zero) combAdd vx vy)
    go (Even xs) (Even ys) = Even (go xs ys)
    go (Odd xs) (Odd ys) = Odd (go xs ys)

instance (Semiring a, Create (ToBinary n), KnownNat n) => Semiring (Square n a) where
  (<.>) = mulMat
  (<+>) = addMat
  one = evalUpd (0,0) (create (ones (fromInteger $ natVal (Proxy :: Proxy n))))
  zero = runIdentity (create (Identity zero))

-- | The 'create_' function is really two functions combined into one:
-- a normal creation function, with the signature:
--
-- >    (∀ b. b -> v b)
-- > -> (∀ b. b -> w b)
-- > -> a
-- > -> Int
-- > -> Square_ n v w a
--
-- And an indexing function for a lens, with the signature:
--
-- >    (∀ b. Int -> Lens (v b) b)
-- > -> (∀ b. Int -> Lens (w b) b)
-- > -> Int -> Int
--
-- building the indexing function allows for sharing between access
-- of different indices.

mkP
  :: Applicative f
  => (f a -> f (v a)) -> (f a -> f (w a)) -> f a -> f (Product v w a)
mkP = (liftA2.liftA2) Pair

-- | Creates a square of side length @n@ from some applicative.
-- >>> create 1 (Just 'a')
  -- Just ["a"]
create :: (Applicative f, Create (ToBinary n)) => f a -> f (Square n a)
create =
    fmap Square . create_ leE leI 0 1 ((const . pure) Proxy) (fmap Identity)


class Create (n :: Binary)  where
    create_
        :: Applicative f
        => (∀ b. Int -> Lens (v b) b)
        -> (∀ b. Int -> Lens (w b) b)
        -> Int
        -> Int
        -> (∀ b. f b -> f (v b))
        -> (∀ b. f b -> f (w b))
        -> f a
        -> f (Square_ n v w a)

instance Create 'Z where
    create_ lev _ _ _ mkv _ = fmap (Zero lev) . mkv . mkv

instance Create n =>
         Create ('O n) where
    create_ lev lew vsz wsz mkv mkw =
        fmap Even .
        create_ lev (leP lew lew wsz) vsz (wsz + wsz) mkv (mkP mkw mkw)

instance Create n =>
         Create ('I n) where
    create_ lev lew vsz wsz mkv mkw =
        fmap Odd .
        create_
            (leP lev lew vsz)
            (leP lew lew wsz)
            (vsz + wsz)
            (wsz + wsz)
            (mkP mkv mkw)
            (mkP mkw mkw)

-- The indexing 'Lens for 'Proxy'. If this is called, it means an
-- invalid index has been given. This is caught earlier with the
-- 'Square' indexing functions.
leE :: Int -> Lens (Proxy a) a
leE _ = undefined

-- The indexing 'Lens for 'Identity'. This should only recieve @0@ as
-- the index, however this is not checked, as it is check earlier.
leI :: Int -> Lens (Identity a) a
leI _ f (Identity x) = Identity <$> f x

-- The indexing 'Lens for a pair.
leP :: (Int -> Lens (v a) a)
    -> (Int -> Lens (w a) a)
    -> Int -> Int -> Lens (Product v w a) a
leP lev lew nv i f (Pair v w)
  | i < nv    = flip Pair w <$> lev i f v
  | otherwise = Pair v <$> lew (i-nv) f w

------------------------------------------------------------------------
-- Indexing
------------------------------------------------------------------------

type FlippedLens s a = ∀ f. Functor f => s -> (a -> f a) -> f s

ix_ :: (Int, Int) -> Lens (Square_ n v w a) a
ix_ (i,j) = flip ix' where
  ix' :: FlippedLens (Square_ n v w a) a
  ix' (Zero lev vv) = \f -> Zero lev <$> (lev i . lev j) f vv
  ix' (Even      m) = fmap Even . ix' m
  ix' (Odd       m) = fmap Odd  . ix' m

alterF
  :: (Applicative f, KnownNat n)
  => (a -> f a) -> (Int, Int) -> Square n a -> f (Square n a)
alterF f (i,j) s@(Square q :: Square n a)
  | i <  0 = pure s
  | j <  0 = pure s
  | i >= n = pure s
  | j >= n = pure s
  | otherwise = Square <$> ix_ (i,j) f q
  where n = fromInteger (natVal (Proxy :: Proxy n))

(!) :: KnownNat n => Square n a -> (Int, Int) -> Maybe a
s ! i = (getFirst .# getConst) ((`alterF` i) (Const .# First .# Just) s)

infixr 9 .#
(.#) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(.#) _ = coerce

------------------------------------------------------------------------
-- Eq and Ord
------------------------------------------------------------------------

instance (Eq1 v, Eq1 w) =>
         Eq1 (Square_ n v w) where
    liftEq eq (Zero _ x) (Zero _ y) = liftEq (liftEq eq) x y
    liftEq eq (Odd x) (Odd y) = liftEq eq x y
    liftEq eq (Even x) (Even y) = liftEq eq x y

instance (Eq1 v, Eq1 w, Eq a) =>
         Eq (Square_ n v w a) where
    (==) = eq1
instance (Ord1 v, Ord1 w, Ord a) =>
         Ord (Square_ n v w a) where
    compare = compare1

instance (Ord1 v, Ord1 w) =>
         Ord1 (Square_ n v w) where
    liftCompare cmp (Zero _ x) (Zero _ y) = (liftCompare . liftCompare) cmp x y
    liftCompare cmp (Odd x) (Odd y) = liftCompare cmp x y
    liftCompare cmp (Even x) (Even y) = liftCompare cmp x y

------------------------------------------------------------------------
-- Show
------------------------------------------------------------------------

instance Show a => Show (Square n a) where
  showsPrec n s = showsPrec n (toList (fmap toList (rows s)))

------------------------------------------------------------------------
-- fromList
------------------------------------------------------------------------

newtype Source s a =
  Source (∀ c. (Maybe a -> [s] -> c) -> [s] -> c)

instance Functor (Source s) where
  fmap f (Source m) = Source (\t -> m (t . fmap f))
  {-# INLINABLE fmap #-}

instance Applicative (Source s) where
  pure x = Source (\t -> t (pure x))
  {-# INLINABLE pure #-}
  Source fs <*> Source xs =
    Source (\t -> fs (\f -> xs (t . (<*>) f)))
  {-# INLINABLE (<*>) #-}

evalSource :: Source s a -> [s] -> Maybe a
evalSource (Source x) = x const
{-# INLINABLE evalSource #-}

fromList :: Create (ToBinary n) => [a] -> Maybe (Square n a)
fromList = evalSource (create (Source uncons')) where
  uncons' f [] = f Nothing []
  uncons' f (x:xs) = f (Just x) xs

newtype Upd a =
  Upd (∀ c. (a -> (Int,Int) -> c) -> (Int,Int) -> c)

instance Functor Upd where
  fmap f (Upd m) = Upd (\t -> m (t . f))
  {-# INLINABLE fmap #-}

instance Applicative Upd where
  pure x = Upd (\t -> t x)
  {-# INLINABLE pure #-}
  Upd fs <*> Upd xs =
    Upd (\t -> fs (\f -> xs (t . f)))
  {-# INLINABLE (<*>) #-}

ones :: (Semiring a) => Int -> Upd a
ones n =
    Upd
        (\f (curcol,col) ->
              if curcol == col
                  then f one (curcol + 1, col)
                  else if curcol == (n - 1)
                           then f zero (0, col + 1)
                           else f zero (curcol + 1, col))

evalUpd :: (Int,Int) -> Upd a -> a
evalUpd x (Upd f) = f const x
