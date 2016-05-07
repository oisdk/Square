{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

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

-- | This type represents a square matrix. In the form:
--
-- > Square_ None Identity a
--
-- It is unable to be a non-square. It is adapted from
-- <http://www.usma.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp99square.pdf Okasaki's>
-- square matrices:
--
-- > data Square_ v w a =
-- >    Zero (v (v a))
-- >  | Even (Square_      v     (Pair w w) a)
-- >  | Odd  (Square_ (Pair v w) (Pair w w) a)
--
-- The extra field in the @Zero@ branch is a function which, when
-- given a valid index, produces a 'Lens' into the element at that
-- position. This could be accomplished without the field, but this
-- way allows sharing of work across repeated access to different
-- indices.

data Square_ v w a =
    Zero (forall b. Int -> Lens' (v b) b) (v (v a))
  | Even (Square_      v     (Pair w w) a)
  | Odd  (Square_ (Pair v w) (Pair w w) a)
  deriving (Functor)

-- In order to store the information in a square, three new types are
-- needed:
--
-- * a type for storing no elements: 'None'
-- * a type for storing one element: 'Identity' (from
-- "Data.Functor.Identity")
-- * a type for storing two sub-trees of elements: 'Pair'

newtype None a = None ()
  deriving (Functor, Foldable, Traversable, Eq, Ord)

data Pair v w a = Pair (v a) (w a)
  deriving (Functor, Foldable, Traversable, Eq, Ord)

mkP :: (a -> v a) -> (a -> w a) -> a -> Pair v w a
mkP mkv mkw x = Pair (mkv x) (mkw x)

-- | @'create' n x@ will create a square, of size @n*n@, containing
-- the repeated element 'x'.

create :: Int -> a -> Square a
create n x =
  Square n (create_ leE leI 0 1 (const $ None ()) Identity x n)

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
-- >    (forall b. Int -> Lens' (v b) b)
-- > -> (forall b. Int -> Lens' (w b) b)
-- > -> Int -> Int
--
-- building the indexing function allows for sharing between access
-- of different indices.

create_ :: (forall b. Int -> Lens' (v b) b)
        -> (forall b. Int -> Lens' (w b) b)
        -> Int -> Int
        -> (forall b. b -> v b)
        -> (forall b. b -> w b)
        -> a
        -> Int
        -> Square_ v w a
create_ lev _ _ _ mkv _ x 0 = Zero lev (mkv (mkv x))
create_ lev lew vsz wsz mkv mkw x n
  | even n =
    Even (create_
          lev (leP lew lew wsz) vsz (wsz+wsz)
          mkv (mkP mkw mkw) x (n `div` 2))
  | otherwise =
    Odd  (create_
          (leP lev lew vsz) (leP lew lew wsz) (vsz+wsz) (wsz+wsz)
          (mkP mkv mkw) (mkP mkw mkw) x (n `div` 2))

-- The indexing 'Lens' for 'None'. If this is called, it means an
-- invalid index has been given. This is caught earlier with the
-- 'Square' indexing functions.
leE :: Int -> Lens' (None a) a
leE _ = undefined

-- The indexing 'Lens' for 'Identity'. This should only recieve @0@ as
-- the index, however this is not checked, as it is check earlier.
leI :: Int -> Lens' (Identity a) a
leI _ f (Identity x) = Identity <$> f x

-- The indexing 'Lens' for a pair.
leP :: (Int -> Lens' (v a) a)
    -> (Int -> Lens' (w a) a)
    -> Int -> Int -> Lens' (Pair v w a) a
leP lev lew nv i f (Pair v w)
  | i < nv    = flip Pair w <$> lev i f v
  | otherwise = Pair v <$> lew (i-nv) f w

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

instance (Traversable v, Traversable w)
  => Traversable (Square_ v w) where
    traverse f (Zero l v) = Zero l <$> (traverse.traverse) f v
    traverse f (Even   v) = Even   <$> traverse            f v
    traverse f (Odd    v) = Odd    <$> traverse            f v

data Square a =
  Square { _squareSize :: Int
         , _square     :: Square_ None Identity a
         } deriving (Functor, Foldable, Traversable)

class Eq1 f => EqR1 f where
  eqr1 :: (Eq a, EqR1 g) => f (g a) -> f (g a) -> Bool

instance EqR1 None where eqr1 _ _ = True

instance (EqR1 v, EqR1 w) => EqR1 (Pair v w) where
  eqr1 (Pair a b) (Pair c d) = eqr1 a c && eqr1 b d

instance (Eq1 v, Eq1 w) => Eq1 (Pair v w) where
  Pair a b ==# Pair c d = a ==# c && b ==# d

instance Eq1 None where _ ==# _ = True

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
    flip (foldr (\e a -> e ('\n':a)))
      [ showList [ m ^. ix_ (i,j) | j <- idxs] | i <- idxs]
        where idxs = [0..(n-1)]

instance Arbitrary a => Arbitrary (Square a) where
  arbitrary = sized (traverse (const arbitrary) . flip create ())

newtype MaybeState s a =
  MaybeState { runMaybeState :: s -> Maybe (s, a)
             } deriving (Functor)

instance Applicative (MaybeState s) where
  pure x = MaybeState (\s -> Just (s, x))
  MaybeState f <*> MaybeState x =
    MaybeState ((\(s,g) -> (fmap.fmap) g (x s)) <=< f)

newtype RecAccu a b =
  RecAccu { runRecAccu :: a -> Maybe (RecAccu a b, b) }

mapAccumM :: Traversable t
          => (a -> b -> Maybe (a, c))
          -> t b -> a -> Maybe (t c)
mapAccumM f t s =
  snd <$> runMaybeState (traverse (MaybeState . flip f) t) s

zipInto :: (Traversable t, Foldable f)
        => (a -> b -> c) -> t a -> f b
        -> Maybe (t c)
zipInto f xs = mapAccumM runRecAccu xs . RecAccu . foldr h i where
  i _ = Nothing
  h e2 a e1 = Just (RecAccu a, f e1 e2)

replace :: (Traversable t, Foldable f) => t a -> f b -> Maybe (t b)
replace = zipInto (\_ x -> x)

fromList :: Foldable f => Int -> f a -> Maybe (Square a)
fromList n = replace (create n ())

unsafeIndex :: Square a -> (Int, Int) -> a
unsafeIndex (Square _ s) i = s ^. ix_ i
