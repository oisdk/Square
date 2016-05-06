{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

-- From Fast Exponentiation to Square Matrices: An Adventure in Types - Okasaki

module Data.Square
  ( Square
  , squareSize
  , _squareSize
  , create
  , fromList
  , unsafeIndex
  ) where

import           Control.Lens
import           Control.Monad   ((<=<))
import           Prelude.Extras
import           Test.QuickCheck

newtype Pair v w a = P (v a, w a)
  deriving (Functor, Foldable, Traversable, Eq, Ord)

data Square_ v w a =
    Zero (forall b. Int -> Lens' (v b) b) (v (v a))
  | Even (Square_ v (Pair w w) a)
  | Odd (Square_ (Pair v w) (Pair w w) a)
  deriving (Functor)

mkP :: (a -> v a) -> (a -> w a) -> a -> Pair v w a
mkP mkv mkw x = P (mkv x, mkw x)

create :: Int -> a -> Square a
create n x = Square n (create_ leE leI 0 1 (const $ EmptyF ()) Identity x n)

create_ :: (forall b. Int -> Lens' (v b) b)
        -> (forall b. Int -> Lens' (w b) b)
        -> Int -> Int
        -> (forall b. b -> v b)
        -> (forall b. b -> w b)
        -> a
        -> Int
        -> Square_ v w a
create_ lev _ _ _ mkv _ x 0 = Zero lev (mkv (mkv x))
create_ lev lew vsize wsize mkv mkw x n
  | even n =
    Even (create_ lev (leP lew lew wsize) vsize (wsize+wsize) mkv (mkP mkw mkw) x (n `div` 2))
  | otherwise =
    Odd  (create_ (leP lev lew vsize) (leP lew lew wsize) (vsize+wsize) (wsize+wsize)
         (mkP mkv mkw) (mkP mkw mkw) x (n `div` 2))

leE :: Int -> Lens' (EmptyF a) a
leE _ _ (EmptyF ()) = undefined

leI :: Int -> Lens' (Identity a) a
leI _ f (Identity x) = Identity <$> f x

leP :: (Int -> Lens' (v a) a)
    -> (Int -> Lens' (w a) a)
    -> Int -> Int -> Lens' (Pair v w a) a
leP lev lew nv i f (P (v,w))
  | i < nv    = P . flip (,) w <$> lev i f v
  | otherwise = P . (,) v <$> lew (i-nv) f w

type FlippedLens' s a = forall f. Functor f => s -> (a -> f a) -> f s

ix_ :: (Int, Int) -> Lens' (Square_ v w a) a
ix_ (i,j) = flip ix' where
  ix' :: FlippedLens' (Square_ v w a) a
  ix' (Zero lev vv) = \f -> Zero lev <$> (lev i . lev j) f vv
  ix' (Even      m) = fmap Even . ix' m
  ix' (Odd       m) = fmap Odd  . ix' m

instance (Foldable v, Foldable w) => Foldable (Square_ v w) where
  foldMap f (Zero _ v) = (foldMap.foldMap) f v
  foldMap f (Even   v) = foldMap f v
  foldMap f (Odd    v) = foldMap f v
  foldr f i (Zero _ v) = foldr (flip $ foldr f) i v
  foldr f i (Even   v) = foldr f i v
  foldr f i (Odd    v) = foldr f i v

instance (Traversable v, Traversable w) => Traversable (Square_ v w) where
  traverse f (Zero l v) = Zero l <$> (traverse.traverse) f v
  traverse f (Even   v) = Even   <$> traverse            f v
  traverse f (Odd    v) = Odd    <$> traverse            f v

data Square a =
  Square { _squareSize :: Int
         , _square :: Square_ EmptyF Identity a
         } deriving (Functor, Foldable, Traversable)

class Eq1 f => EqR1 f where
  eqr1 :: (Eq a, EqR1 g) => f (g a) -> f (g a) -> Bool

instance EqR1 EmptyF where eqr1 _ _ = True

instance (EqR1 v, EqR1 w) => EqR1 (Pair v w) where
  eqr1 (P (a,b)) (P (c,d)) = eqr1 a c && eqr1 b d

instance (Eq1 v, Eq1 w) => Eq1 (Pair v w) where
  P (a,b) ==# P (c,d) = a ==# c && b ==# d

newtype EmptyF a = EmptyF ()
  deriving (Functor, Foldable, Traversable, Eq, Ord)

instance Eq1 EmptyF where _ ==# _ = True

instance EqR1 Identity where
  eqr1 (Identity a) (Identity b) = a ==# b

instance (EqR1 v, EqR1 w) => Eq1 (Square_ v w) where
  Zero _ x ==# Zero _ y = eqr1 x y
  Odd    x ==# Odd    y = x ==# y
  Even   x ==# Even   y = x ==# y
  _        ==# _        = False

instance Eq a => Eq (Square a) where
  Square n v == Square m w = n == m && v ==# w

instance Eq1 Square where
  Square n v ==# Square m w = n == m && v ==# w

instance Ixed (Square a) where
  ix (i,j) f (Square n m)
    | i >= n    = pure (Square n m)
    | j >= n    = pure (Square n m)
    | otherwise = Square n <$> ix_ (i,j) f m

type instance Index (Square a) = (Int, Int)
type instance IxValue (Square a) = a

squareSize :: Getter (Square a) Int
squareSize = to _squareSize

instance Show a => Show (Square a) where
  showsPrec _ (Square n m) =
    flip (foldr (\e a -> e ('\n':a))) [ showList [ m ^. ix_ (i,j) | j <- idxs] | i <- idxs]
      where idxs = [0..(n-1)]

instance Arbitrary a => Arbitrary (Square a) where
  arbitrary = sized (traverse (const arbitrary) . flip create ())

newtype MaybeState s a =
  MaybeState { runMaybeState :: s -> Maybe (s, a)
             } deriving (Functor)

instance Applicative (MaybeState s) where
  pure x = MaybeState (\s -> Just (s, x))
  MaybeState f <*> MaybeState x = MaybeState ((\(s,g) -> (fmap.fmap) g (x s)) <=< f)

newtype RecAccu a b =
  RecAccu { runRecAccu :: a -> Maybe (RecAccu a b, b) }

mapAccumL :: Traversable t => (a -> b -> Maybe (a, c)) -> t b -> a -> Maybe (t c)
mapAccumL f t s = snd <$> runMaybeState (traverse (MaybeState . flip f) t) s

zipInto :: (Traversable t, Foldable f)
        => (a -> b -> c) -> t a -> f b
        -> Maybe (t c)
zipInto f xs = mapAccumL runRecAccu xs . RecAccu . foldr h i where
  i _ = Nothing
  h e2 a e1 = Just (RecAccu a, f e1 e2)

replace :: (Traversable t, Foldable f) => t a -> f b -> Maybe (t b)
replace = zipInto (\_ x -> x)

fromList :: Foldable f => Int -> f a -> Maybe (Square a)
fromList n = replace (create n ())

unsafeIndex :: Square a -> (Int, Int) -> a
unsafeIndex (Square _ s) i = s ^. ix_ i
