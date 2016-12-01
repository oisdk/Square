{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

module Data.Square
  ( Square
  , create
  , alterF
  , fromList
  , (!)
  , squareSize
  ) where

import           Control.Applicative
import           Data.Coerce
import           Data.Functor.Classes
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.List
import           Data.Monoid           hiding (Product (..))
import           Data.Proxy

-- | This type represents a square matrix. In the form:
--
-- > Square_ Proxy Identity a
--
-- It is unable to be a non-square. It is adapted from
-- <http://www.usma.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp99square.pdf Okasaki's>
-- square matrices:
--
-- > data Square_ v w a =
-- >    Zero (v (v a))
-- >  | Even (Square_      v     (Product w w) a)
-- >  | Odd  (Square_ (Product v w) (Product w w) a)
--
-- The extra field in the @Zero@ branch is a function which, when
-- given a valid index, produces a Lens into the element at that
-- position. This could be accomplished without the field, but this
-- way allows sharing of work across repeated access to different
-- indices.
data Square a =
  Square { squareSize :: Int
         , _square    :: Square_ Proxy Identity a
         } deriving (Functor, Traversable)

instance Foldable Square where
  foldr f i (Square _ s) = foldr f i s
  foldMap f (Square _ s) = foldMap f s
  length    (Square n _) = n * n

type Lens s a = forall f. Functor f => (a -> f a) -> s -> f s

data Square_ v w a =
    Zero (forall b. Int -> Lens (v b) b) (v (v a))
  | Even (Square_          v    (Product w w) a)
  | Odd  (Square_ (Product v w) (Product w w) a)
  deriving (Functor)

-- | The 'create_' function is really two functions combined into one:
-- a normal creation function, with the signature:
--
-- >    (forall b. b -> v b)
-- > -> (forall b. b -> w b)
-- > -> a
-- > -> Int
-- > -> Square_ v w a
--
-- And an indexing function for a lens, with the signature:
--
-- >    (forall b. Int -> Lens (v b) b)
-- > -> (forall b. Int -> Lens (w b) b)
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
create ::Applicative f => Int -> f a -> f (Square a)
create n =
  fmap (Square n) .
  create_ leE leI 0 1 ((const.pure) Proxy) (fmap Identity) n

create_ :: Applicative f
        => (forall b. Int -> Lens (v b) b)
        -> (forall b. Int -> Lens (w b) b)
        -> Int -> Int
        -> (forall b. f b -> f (v b))
        -> (forall b. f b -> f (w b))
        -> Int
        -> f a
        -> f (Square_ v w a)
create_ lev _ _ _ mkv _ 0 = fmap (Zero lev) . mkv . mkv
create_ lev lew vsz wsz mkv mkw n
  | even n = fmap Even .
    create_
      lev (leP lew lew wsz) vsz (wsz+wsz)
      mkv (mkP mkw mkw) (n `div` 2)
  | otherwise = fmap Odd .
    create_
      (leP lev lew vsz) (leP lew lew wsz) (vsz+wsz) (wsz+wsz)
      (mkP mkv mkw) (mkP mkw mkw) (n `div` 2)

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

type FlippedLens s a = forall f. Functor f => s -> (a -> f a) -> f s

ix_ :: (Int, Int) -> Lens (Square_ v w a) a
ix_ (i,j) = flip ix' where
  ix' :: FlippedLens (Square_ v w a) a
  ix' (Zero lev vv) = \f -> Zero lev <$> (lev i . lev j) f vv
  ix' (Even      m) = fmap Even . ix' m
  ix' (Odd       m) = fmap Odd  . ix' m

alterF
  :: Applicative f
  => (a -> f a) -> (Int, Int) -> Square a -> f (Square a)
alterF f (i,j) s@(Square n q)
  | i <  0 = pure s
  | j <  0 = pure s
  | i >= n = pure s
  | j >= n = pure s
  | otherwise = Square n <$> ix_ (i,j) f q

(!) :: Square a -> (Int, Int) -> Maybe a
s ! i = (getFirst .# getConst) ((`alterF` i) (Const .# First .# Just) s)

infixr 9 .#
(.#) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(.#) _ = coerce

------------------------------------------------------------------------
-- Foldable and Traversable
------------------------------------------------------------------------

instance (Foldable v, Foldable w) => Foldable (Square_ v w) where
  foldMap f (Zero _ v) = (foldMap.foldMap) f v
  foldMap f (Even   v) = foldMap f v
  foldMap f (Odd    v) = foldMap f v
  foldr f i (Zero _ v) = foldr (flip $ foldr f) i v
  foldr f i (Even   v) = foldr f i v
  foldr f i (Odd    v) = foldr f i v

instance (Traversable v, Traversable w)
  => Traversable (Square_ v w) where
    traverse f (Zero l v) = Zero l <$> (traverse.traverse) f v
    traverse f (Even   v) = Even   <$> traverse            f v
    traverse f (Odd    v) = Odd    <$> traverse            f v

------------------------------------------------------------------------
-- Eq and Ord
------------------------------------------------------------------------

instance (Eq1 v, Eq1 w) => Eq1 (Square_ v w) where
  liftEq eq (Zero _ x) (Zero _ y) = liftEq (liftEq eq) x y
  liftEq eq (Odd    x) (Odd    y) = liftEq eq x y
  liftEq eq (Even   x) (Even   y) = liftEq eq x y
  liftEq _   _          _         = False

instance Eq a => Eq (Square a) where
  Square n v == Square m w = n == m && eq1 v w

instance Eq1 Square where
  liftEq eq (Square n v) (Square m w) = n == m && liftEq eq v w

instance (Ord1 v, Ord1 w) => Ord1 (Square_ v w) where
  liftCompare cmp (Zero _ x) (Zero _ y) =
    (liftCompare.liftCompare) cmp x y
  liftCompare cmp (Odd    x) (Odd    y) = liftCompare cmp x y
  liftCompare cmp (Even   x) (Even   y) = liftCompare cmp x y
  -- Differently sized squares are compared on their sizes
  liftCompare _  _          _         = undefined

instance Ord a => Ord (Square a) where
  compare (Square n v) (Square m w) = compare n m <> compare1 v w

instance Ord1 Square where
  liftCompare cmp (Square n v) (Square m w) =
    compare n m <> liftCompare cmp v w

groupTo :: Int -> [a] -> [[a]]
groupTo n = unfoldr $ \case
  [] -> Nothing
  xs -> Just (splitAt n xs)

------------------------------------------------------------------------
-- Show
------------------------------------------------------------------------

instance Show a => Show (Square a) where
  showsPrec n s =
    showsPrec n . groupTo (squareSize s) . foldr (:) [] $ s

------------------------------------------------------------------------
-- fromList
------------------------------------------------------------------------

newtype Source s a =
  Source (forall c. (Maybe a -> List s -> c) -> List s -> c)

instance Functor (Source s) where
  fmap f (Source m) = Source (\t -> m (t . fmap f))
  {-# INLINABLE fmap #-}

instance Applicative (Source s) where
  pure x = Source (\t -> t (pure x))
  {-# INLINABLE pure #-}
  Source fs <*> Source xs =
    Source (\t -> fs (\f -> xs (t . (<*>) f)))
  {-# INLINABLE (<*>) #-}

evalSource :: Source s a -> List s -> Maybe a
evalSource (Source x) = x const
{-# INLINABLE evalSource #-}

newtype List a =
  List (forall b. b -> (a -> List a -> b) -> b)

fromList :: Foldable f => Int -> f a -> Maybe (Square a)
fromList n = evalSource (create n pop) . foldr cons nil where
  cons y ys = List (const (\g -> g y ys))
  nil = List const
  pop = Source (\t (List l) -> l (t Nothing nil) (t . Just))
