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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Square
  (Square
  ,rows
  ,transpose
  ,cols
  ,fromList
  ,create
  ,alterF
  , Indexable
  ,(!)
  ,KnownDimension
  ,Creatable)
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
import Data.Traversable

-- $setup
-- >>> :set -XDataKinds


data Dimension = Linear | Project Dimension
data Binary = Z | O Binary | I Binary

data Nested :: Dimension -> (* -> *) -> * -> * where
  Flat :: a -> Nested 'Linear f a
  Embd :: f (Nested n f a) -> Nested ('Project n) f a

class Tupleable (c :: Dimension) where
  type Tuple c a :: *
  fromTuple :: Tuple c a -> Nested c ((,) a) ()

type Indexable n = Tupleable (ToDimension n)
type KnownDimension n = Expandable (ToDimension n)

instance Tupleable 'Linear where
  type Tuple 'Linear a = ()
  fromTuple _ = Flat ()

instance Tupleable ('Project 'Linear) where
  type Tuple ('Project 'Linear) a = a
  fromTuple x = Embd (x,Flat ())

instance Tupleable ('Project ('Project 'Linear)) where
  type Tuple ('Project ('Project 'Linear)) a = (a,a)
  fromTuple (x,y) = Embd (x,Embd (y, Flat ()))

instance Tupleable ('Project ('Project ('Project 'Linear))) where
  type Tuple ('Project ('Project ('Project 'Linear))) a = (a,a,a)
  fromTuple (x,y,z) = Embd (x,Embd (y, Embd (z,Flat ())))

appN
    :: Applicative f
    => (i -> (forall b. (b -> f b) -> (v b -> f (v b))))
    -> Nested c ((,) i) ()
    -> (a -> f a)
    -> Nested c v a
    -> f (Nested c v a)
appN _ (Flat _) f (Flat x) = fmap Flat (f x)
appN l (Embd (i,x)) f (Embd y) = fmap Embd (l i (appN l x f) y)

itraverseN
    :: Traversable f
    => (Nested c ((,) Integer) () -> a -> b) -> Nested c f a -> Nested c f b
itraverseN f (Flat x) = Flat (f (Flat ()) x)
itraverseN f (Embd x) =
    Embd
        (snd $
         mapAccumL
             (\acc val ->
                   ( acc + 1
                   , itraverseN
                         (\n y ->
                               f (Embd (acc, n)) y)
                         val))
             0
             x)

allEq :: Eq a => Nested c ((,) a) () -> Bool
allEq (Flat ()) = True
allEq (Embd (_,Flat ())) = True
allEq (Embd (x, Embd (y, z))) = x == y && allEq (Embd (y,z))

embdL :: Functor f => Nested c f (f a) -> Nested ('Project c) f a
embdL (Flat x) = Embd (fmap Flat x)
embdL (Embd x) = Embd (fmap embdL x)

instance (Show1 f, Show a) => Show (Nested s f a) where
  showsPrec = showsPrec1

instance Show1 f => Show1 (Nested s f) where
  liftShowsPrec f _ d (Flat x) =
      f d x
  liftShowsPrec f g d (Embd x) =
      liftShowsPrec (liftShowsPrec f g) (liftShowList f g) d x

instance Eq1 f => Eq1 (Nested c f) where
  liftEq eq (Flat x) (Flat y) = eq x y
  liftEq eq (Embd x) (Embd y) = liftEq (liftEq eq) x y

instance Ord1 f => Ord1 (Nested c f) where
  liftCompare cmp (Flat x) (Flat y) = cmp x y
  liftCompare cmp (Embd x) (Embd y) = liftCompare (liftCompare cmp) x y

instance (Eq1 f, Eq a) => Eq (Nested c f a) where (==) = eq1
instance (Ord1 f, Ord a) => Ord (Nested c f a) where compare = compare1

class Expandable (c :: Dimension) where
  liftMake :: Functor f => (∀ a. f a -> f (v a)) -> f b -> f (Nested c v b)
  liftAp :: Applicative f => Nested c f (a -> b) -> Nested c f a -> Nested c f b
  transposeN :: (Applicative f, Traversable f) => Nested c f a -> Nested c f a
  matMul :: (Semiring a, Applicative f, Traversable f) => Nested c f a -> Nested c f a -> Nested c f a

instance (Applicative f, Expandable c) => Applicative (Nested c f) where
  pure x = runIdentity (liftMake (fmap pure) (Identity x))
  (<*>) = liftAp

instance Expandable 'Linear where
  liftMake _ = fmap Flat
  liftAp (Flat fs) (Flat xs) = Flat (fs xs)
  transposeN = id
  matMul (Flat x) (Flat y) = Flat (x <.> y)

instance Expandable ('Project 'Linear) where
  liftMake f x = fmap Embd (f (liftMake f x))
  liftAp (Embd fs) (Embd xs) = Embd (liftA2 liftAp fs xs)
  transposeN (Embd x) = embdL (traverse transposeN x)
  matMul (Embd xs) (Embd ys) = Embd (liftA2 matMul xs ys)

instance (Expandable n, Expandable ('Project n)) => Expandable ('Project ('Project n)) where
  liftMake f x = fmap Embd (f (liftMake f x))
  liftAp (Embd fs) (Embd xs) = Embd (liftA2 liftAp fs xs)
  transposeN (Embd x) = embdL (traverse transposeN x)
  matMul (Embd xs) y = case transposeN y of
    Embd ys -> Embd (fmap (`mul1` ys) xs)

getEmbd :: Nested ('Project n) f a -> f (Nested n f a)
getEmbd (Embd x) = x

mul1
    :: (Applicative f
       ,Traversable f
       ,Semiring a
       ,Expandable n)
    => Nested ('Project n) f a
    -> f (Nested ('Project n) f a)
    -> Nested ('Project n) f a
mul1 (Embd x) y = Embd (mull x (fmap getEmbd y))

mull
    :: (Applicative f, Traversable f, Semiring a, Expandable n)
    => f (Nested n f a) -> f (f (Nested n f a)) -> f (Nested n f a)
mull (xr :: f (Nested n f a)) = fmap (add . liftA2 (<.>) xr)

instance (Expandable n, Applicative f, Semiring a, Traversable f) => Semiring (Nested n f a) where
  zero = pure zero
  (<+>) = liftA2 (<+>)
  one = itraverseN (\i v -> if allEq i then one else v) zero
  (<.>) = matMul

transpose
    :: Expandable (ToDimension c)
    => Square c n a -> Square c n a
transpose (Square s) = Square (go s)
  where
    go
        :: (Applicative v
           ,Traversable v
           ,Expandable c
           ,Applicative w
           ,Traversable w)
        => Square_ c n v w a -> Square_ c n v w a
    go (Zero l x) = Zero l (transposeN x)
    go (Even x) = Even (go x)
    go (Odd x) = Odd (go x)

type f ~> g = ∀ a. f a -> g a

liftFmap :: Functor f => (f ~> g) -> Nested c f a -> Nested c g a
liftFmap _ (Flat x) = Flat x
liftFmap f (Embd x) = Embd (f (fmap (liftFmap f) x))

instance Functor f => Functor (Nested d f) where
  fmap f (Flat x) = Flat (f x)
  fmap f (Embd x) = Embd ((fmap.fmap) f x)

instance Foldable f => Foldable (Nested d f) where
  foldMap f (Flat x) = f x
  foldMap f (Embd x) = (foldMap.foldMap) f x

instance Traversable f => Traversable (Nested d f) where
  traverse f (Flat x) = fmap Flat (f x)
  traverse f (Embd x) = fmap Embd ((traverse.traverse) f x)

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

type family ToDimension (n :: Nat) :: Dimension where
  ToDimension 0 = 'Linear
  ToDimension n = 'Project (ToDimension (n-1))

-- | This type represents a square matrix. In the form:
--
-- > Square_ Proxy Identity a
--
-- It is unable to be a non-square. It is adapted from
-- <http://www.usma.edu/eecs/SiteAssets/SitePages/Faculty%20Publication%20Documents/Okasaki/icfp99square.pdf Okasaki's>
-- square matrices:
--
-- > data Square_ c n v w a =
-- >    Zero (v (v a))
-- >  | Even (Square_      v     (Product w w) a)
-- >  | Odd  (Square_ (Product v w) (Product w w) a)
--
-- The extra field in the @Zero@ branch is a function which, when
-- given a valid index, produces a Traversal into the element at that
-- position. This could be accomplished without the field, but this
-- way allows sharing of work across repeated access to different
-- indices.
newtype Square c n a =
  Square { _getSquare :: Square_ (ToDimension c) (ToBinary n) Proxy Identity a
         }  deriving (Functor, Foldable, Traversable, Eq, Ord, Eq1, Ord1)

type Traversal s a = ∀ f. Applicative f => (a -> f a) -> s -> f s

data Square_ :: Dimension -> Binary -> (* -> *) -> (* -> *) -> * -> * where
  Zero :: (∀ b. Int -> Traversal (v b) b) -> Nested c v a -> Square_ c 'Z v w a
  Even :: Square_ c n          v    (Product w w) a   -> Square_ c ('O n) v w a
  Odd  :: Square_ c n (Product v w) (Product w w) a   -> Square_ c ('I n) v w a

deriving instance (Functor v, Functor w) => Functor (Square_ c n v w)
deriving instance (Foldable v, Foldable w) => Foldable (Square_ c n v w)
deriving instance (Traversable v, Traversable w) => Traversable (Square_ c n v w)

instance (Create (ToBinary n), Expandable (ToDimension c), Semiring a) => Semiring (Square c n a) where
  one = let z = zero in Square (imap_ (\i v -> if allEq i then one else v) (_getSquare z)) `asTypeOf` z
  zero = pure zero
  (<+>) = liftA2 (<+>)
  Square xs <.> Square ys = Square (go xs ys) where
    go :: forall d s w v. (Expandable d, Applicative w, Applicative v, Traversable w, Traversable v) =>
      Square_ d s v w a -> Square_ d s v w a -> Square_ d s v w a
    go (Zero xl xv) (Zero _ yv) = Zero xl (xv <.> yv)
    go (Even x) (Even y) = Even (go x y)
    go (Odd x) (Odd y) = Odd (go x y)

newtype FreeMonoid a = FreeMonoid { runFree :: ∀ b. Monoid b => (a -> b) -> b }
instance Show1 FreeMonoid where
  liftShowsPrec _ f _ = f . toList

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

rows :: Square c n a -> Nested (ToDimension c) FreeMonoid a
rows (Square xs) = go toFreeMonoid xs where
  go
      :: forall w v c n. (Foldable w, Foldable v, Functor v, Functor w)
      => (forall a. v a -> FreeMonoid a) -> (forall a. Square_ c n v w a -> Nested c FreeMonoid a)
  go f (Zero _ x) = liftFmap f x
  go f (Even s) = go f s
  go f (Odd s) = go (\(Pair vs ws) -> f vs <> toFreeMonoid ws) s

cols :: Expandable (ToDimension c) => Square c n a -> Nested (ToDimension c) FreeMonoid a
cols = rows . transpose

instance (Creatable n, Expandable (ToDimension c)) =>
         Applicative (Square c n) where
    pure =
        (coerce :: (Identity a -> Identity (Square c n a)) -> a -> Square c n a)
            create
    Square fs <*> Square xs = Square (go fs xs)
      where
        go
            :: forall m v w a b.
               (Applicative v, Applicative w)
            => Square_ (ToDimension c) m v w (a -> b) -> Square_ (ToDimension c) m v w a -> Square_ (ToDimension c) m v w b
        go (Zero _ vx) (Zero ly vy) = Zero ly (vx <*> vy)
        go (Even f) (Even x) = Even (go f x)
        go (Odd f) (Odd x) = Odd (go f x)

-- | The 'create_' function is really two functions combined into one:
-- a normal creation function, with the signature:
--
-- >    (∀ b. b -> v b)
-- > -> (∀ b. b -> w b)
-- > -> a
-- > -> Int
-- > -> Square_ c n v w a
--
-- And an indexing function for a lens, with the signature:
--
-- >    (∀ b. Int -> Traversal (v b) b)
-- > -> (∀ b. Int -> Traversal (w b) b)
-- > -> Int -> Int
--
-- building the indexing function allows for sharing between access
-- of different indices.

mkP
  :: Applicative f
  => (f a -> f (v a)) -> (f a -> f (w a)) -> f a -> f (Product v w a)
mkP = (liftA2.liftA2) Pair

-- | Creates a square of side length @n@ from some applicative.
-- >>> create (Just 'a') :: Maybe (Square 1 Char)
  -- Just ["a"]
create :: (Applicative f, Creatable n, Expandable (ToDimension c)) =>  f a -> f (Square c n a)
create =
    fmap Square . create_ leE leI 0 1 ((const . pure) Proxy) (fmap Identity)


class Create (n :: Binary)  where
    create_
        :: (Applicative f, Expandable c)
        => (∀ b. Int -> Traversal (v b) b)
        -> (∀ b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (∀ b. f b -> f (v b))
        -> (∀ b. f b -> f (w b))
        -> f a
        -> f (Square_ c n v w a)

instance Create 'Z where
    create_ lev _ _ _ mkv _ = fmap (Zero lev) . liftMake mkv

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

type Creatable n = Create (ToBinary n)

-- The indexing 'Traversal' for 'Proxy'. If this is called, it means an
-- invalid index has been given. This is caught earlier with the
-- 'Square' indexing functions.
leE :: Int -> Traversal (Proxy a) a
leE _ _ _ = pure Proxy

-- The indexing 'Traversal for 'Identity'.
leI :: Int -> Traversal (Identity a) a
leI 0 f (Identity x) = Identity <$> f x
leI _ _ i = pure i

-- The indexing 'Traversal for a pair.
leP :: (Int -> Traversal (v a) a)
    -> (Int -> Traversal (w a) a)
    -> Int -> Int -> Traversal (Product v w a) a
leP lev lew nv i f (Pair v w)
  | i < nv    = flip Pair w <$> lev i f v
  | otherwise = Pair v <$> lew (i-nv) f w

------------------------------------------------------------------------
-- Indexing
------------------------------------------------------------------------

type FlippedTraversal s a = ∀ f. Applicative f => s -> (a -> f a) -> f s

ix_ :: Nested c ((,) Int) () -> Traversal (Square_ c n v w a) a
ix_ = flip . ix' where
  ix' :: Nested c ((,) Int) () -> FlippedTraversal (Square_ c n v w a) a
  ix' i (Zero lev vv) = \f -> fmap (Zero lev) (appN lev i f vv)
  ix' i (Even      m) = fmap Even . ix' i m
  ix' i (Odd       m) = fmap Odd  . ix' i m

imap_ :: (Traversable v, Traversable w) => (Nested c ((,) Integer) () -> a -> b) -> Square_ c n v w a -> Square_ c n v w b
imap_ f (Zero lev vv) = Zero lev (itraverseN f vv)
imap_ f (Even vv) = Even (imap_ f vv)
imap_ f (Odd vv) = Odd (imap_ f vv)

alterF
  :: (Applicative f, (Indexable c))
  => (a -> f a) -> Tuple (ToDimension c) Int -> Square c n a -> f (Square c n a)
alterF f i (Square q :: Square c n a)
  = Square <$> ix_ (fromTuple i) f q

(!) :: (Indexable c) => Square c n a -> Tuple (ToDimension c) Int -> Maybe a
s ! i = (getFirst .# getConst) ((`alterF` i) (Const .# First .# Just) s)

infixr 9 .#
(.#) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(.#) _ = coerce

------------------------------------------------------------------------
-- Eq and Ord
------------------------------------------------------------------------

instance (Eq1 v, Eq1 w) =>
         Eq1 (Square_ c n v w) where
    liftEq eq (Zero _ x) (Zero _ y) = liftEq eq x y
    liftEq eq (Odd x) (Odd y) = liftEq eq x y
    liftEq eq (Even x) (Even y) = liftEq eq x y

instance (Eq1 v, Eq1 w, Eq a) =>
         Eq (Square_ c n v w a) where
    (==) = eq1

instance (Ord1 v, Ord1 w, Ord a) =>
         Ord (Square_ c n v w a) where
    compare = compare1

instance (Ord1 v, Ord1 w) =>
         Ord1 (Square_ c n v w) where
    liftCompare cmp (Zero _ x) (Zero _ y) = liftCompare cmp x y
    liftCompare cmp (Odd x) (Odd y) = liftCompare cmp x y
    liftCompare cmp (Even x) (Even y) = liftCompare cmp x y

------------------------------------------------------------------------
-- Show
------------------------------------------------------------------------

instance Show a => Show (Square c n a) where
  showsPrec n = showsPrec n . rows

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

fromList :: (Creatable n, Expandable (ToDimension c)) => [a] -> Maybe (Square c n a)
fromList = evalSource (create (Source uncons')) where
  uncons' f [] = f Nothing []
  uncons' f (x:xs) = f (Just x) xs
