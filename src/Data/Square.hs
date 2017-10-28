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

module Data.Square
  ( -- * The Square type
   Square
  ,Creatable
    -- * Construction
  ,fromList
  ,create
  ,replicate
  ,unfold
  ,unfoldMay
   -- * Conversion
  ,rows
  ,cols
   -- * Indexing
  ,alterF
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
import Data.Foldable
import GHC.TypeLits
import Control.DeepSeq
import Data.Semiring hiding (rows, cols)
import qualified Data.Semiring as Semiring

import Prelude hiding (replicate)
import Data.List (uncons)

import Data.Square.Internal.Binary
import Data.Bits
-- $setup
-- >>> :set -XDataKinds

--------------------------------------------------------------------------------
-- Type definition
--------------------------------------------------------------------------------

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
-- >  | Even (Square_          v    (Product w w) a)
-- >  | Odd  (Square_ (Product v w) (Product w w) a)
--
-- The extra field in the @Zero@ branch is a function which, when
-- given a valid index, produces a Traversal into the element at that
-- position. This could be accomplished without the field, but this
-- way allows sharing of work across repeated access to different
-- indices.
newtype Square n a =
    Square (Square_ (ToBinary n) Proxy Identity a)
    deriving (Functor,Foldable,Traversable,Eq,Ord,Eq1,Ord1,NFData1,NFData)


type Traversal s a = ∀ f. Applicative f => (a -> f a) -> s -> f s

data Square_ n v w a where
        Zero :: (forall b . Int -> Traversal (v b) b) -> v (v a) -> Square_ 'Z v w a
        Even :: !(Square_ n v (Product w w) a) -> Square_ ('O n) v w a
        Odd :: !(Square_ n (Product v w) (Product w w) a) -> Square_ ('I n) v w a

--------------------------------------------------------------------------------
-- Derivations
--------------------------------------------------------------------------------
deriving instance (Functor v, Functor w) => Functor (Square_ n v w)
deriving instance (Foldable v, Foldable w) => Foldable (Square_ n v w)
deriving instance (Traversable v, Traversable w) => Traversable (Square_ n v w)

--------------------------------------------------------------------------------
-- Creation
--------------------------------------------------------------------------------

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
  | i < nv = flip Pair w <$> lev i f v
  | otherwise = Pair v <$> lew (i - nv) f w

mkP
  :: Applicative f
  => (Product v w a -> b) -> (f a -> f (v a)) -> (f a -> f (w a)) -> f a -> f b
mkP k = (liftA2.liftA2) (\x y -> k (Pair x y))

class Create (n :: Binary)  where
    create_
        :: Applicative f
        => (Square_ n v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> f b -> f d)
        -> (forall b. f b -> f (w b))
        -> f a
        -> f c

-- type Create_ n f a
--     =  forall v w c.
--        (Square_ n v w a -> c)
--     -> (forall b. Int -> Traversal (v b) b)
--     -> (forall b. Int -> Traversal (w b) b)
--     -> Int
--     -> Int
--     -> (forall b d. (v b -> d) -> f b -> f d)
--     -> (forall b. f b -> f (w b))
--     -> f a
--     -> f c

instance Create 'Z where
    create_ k lev _ _ _ mkv _ = mkv (k . Zero lev) . mkv id
    {-# INLINE create_ #-}

instance Create n =>
         Create ('O n) where
    create_ k lev lew vsz wsz mkv mkw =
        create_
            (k . Even)
            lev
            (leP lew lew wsz)
            vsz
            (wsz + wsz)
            mkv
            (mkP id mkw mkw)
    {-# INLINE create_ #-}

instance Create n =>
         Create ('I n) where
    create_ k lev lew vsz wsz mkv mkw =
        create_
            (k . Odd)
            (leP lev lew vsz)
            (leP lew lew wsz)
            (vsz + wsz)
            (wsz + wsz)
            (\c -> mkP c (mkv id) mkw)
            (mkP id mkw mkw)
    {-# INLINE create_ #-}

type Creatable n = Create (ToBinary n)

-- | Creates a square of side length @n@ from some applicative.
--
-- >>> create (Just 'a') :: Maybe (Square 1 Char)
-- Just ["a"]
create :: (Applicative f, Creatable n) => f a -> f (Square n a)
create =
    create_ Square leE leI 0 1 (\k -> (const . pure) (k Proxy)) (fmap Identity)
{-# INLINE create #-}

--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

-- | @'row' n@ creates a traversal into the @n@th row of the square.
row :: Int -> Traversal (Square n a) a
row i fs (Square s) = go Square fs s
  where
    go
        :: (Traversable v, Traversable w, Applicative f)
        => (Square_ n v w a -> b) -> (a -> f a) -> Square_ n v w a -> f b
    go k f (Zero lev vv) = fmap (k . Zero lev) ((lev i . traverse) f vv)
    go k f (Even x) = go (k . Even) f x
    go k f (Odd x) = go (k . Odd) f x
{-# INLINE row #-}

-- | @'col' n@ creates a traversal into the @n@th column of the square.
col :: Int -> Traversal (Square n a) a
col i fs (Square s) = go Square fs s
  where
    go
        :: (Traversable v, Traversable w, Applicative f)
        => (Square_ n v w a -> b) -> (a -> f a) -> Square_ n v w a -> f b
    go k f (Zero lev vv) = fmap (k . Zero lev) ((traverse . lev i) f vv)
    go k f (Even x) = go (k . Even) f x
    go k f (Odd x) = go (k . Odd) f x
{-# INLINE col #-}

ix_ :: (Int, Int) -> Traversal (Square_ n v w a) a
ix_ (i,j) (f :: a -> f a) = ix' id where
  ix' :: ∀ b n v w. (Square_ n v w a -> b) -> Square_ n v w a -> f b
  ix' k (Zero lev vv) = (k . Zero lev) <$> (lev i . lev j) f vv
  ix' k (Even      m) = ix' (k . Even) m
  ix' k (Odd       m) = ix' (k . Odd) m
{-# INLINE ix_ #-}

-- | Traverse a given point in the square.
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
{-# INLINE alterF #-}

-- | Index into a given point in the square.
(!) :: KnownNat n => Square n a -> (Int, Int) -> Maybe a
s ! i = (getFirst #. getConst #. alterF (Const #. First #. Just) i) s
{-# INLINE (!) #-}

--------------------------------------------------------------------------------
-- Eq, Ord and Show
--------------------------------------------------------------------------------

instance (Eq1 v, Eq1 w) =>
         Eq1 (Square_ n v w) where
    liftEq (eq :: a -> b -> Bool) = go
      where
        go
            :: forall vv ww nn.
               (Eq1 vv, Eq1 ww)
            => Square_ nn vv ww a -> Square_ nn vv ww b -> Bool
        go (Zero _ x) (Zero _ y) = liftEq (liftEq eq) x y
        go (Odd x) (Odd y) = go x y
        go (Even x) (Even y) = go x y

instance (Eq1 v, Eq1 w, Eq a) =>
         Eq (Square_ n v w a) where
    (==) = eq1

instance (Ord1 v, Ord1 w) =>
         Ord1 (Square_ n v w) where
    liftCompare (cmp :: a -> b -> Ordering) = go
      where
        go
            :: forall vv ww nn.
               (Ord1 vv, Ord1 ww)
            => Square_ nn vv ww a -> Square_ nn vv ww b -> Ordering
        go (Zero _ x) (Zero _ y) = liftCompare (liftCompare cmp) x y
        go (Odd x) (Odd y) = go x y
        go (Even x) (Even y) = go x y

instance (Ord1 v, Ord1 w, Ord a) =>
         Ord (Square_ n v w a) where
    compare = compare1

instance Show a => Show (Square n a) where
  showsPrec n = showsPrec n . rows

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Create a square by replicating a value.
replicate :: Creatable n => a -> Square n a
replicate x = runIdentity #$ create (Identity #$ x)

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

-- | Create a square using a seed value and an unfolding function.
unfold :: Creatable n => (b -> (a, b)) -> b -> Square n a
unfold f = evalState (create (State #$ f))

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

-- | Create a square from a seed value and an unfolding function, returning
-- 'Nothing' if the unfolding function does.
unfoldMay :: Creatable n => (b -> Maybe (a, b)) -> b -> Maybe (Square n a)
unfoldMay f = evalMaybeState (create (MaybeState f))

-- | Create a square from a list, returning 'Nothing' if the list is too short.
fromList :: Creatable n => [a] -> Maybe (Square n a)
fromList = unfoldMay uncons

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

viewInner :: (forall f. Foldable f => f (f a) -> b) -> Square n a -> b
viewInner (f :: forall f. Foldable f => f (f a) -> b) (Square xs) = go xs
  where
    go
        :: forall v w n.
           (Foldable v, Foldable w)
        => Square_ n v w a -> b
    go (Zero _ vs) = f vs
    go (Even s) = go s
    go (Odd s) = go s
{-# INLINE viewInner #-}

-- |
-- >>> fmap rows (fromList [1,2,3,4] :: Maybe (Square 2 Integer))
-- Just [[1,2],[3,4]]
rows :: Square n a -> [[a]]
rows = viewInner (Semiring.rows .# Matrix)

-- |
-- >>> fmap cols (fromList [1,2,3,4] :: Maybe (Square 2 Integer))
-- Just [[1,3],[2,4]]
cols :: Square n a -> [[a]]
cols = viewInner (Semiring.cols .# Matrix)

--------------------------------------------------------------------------------
-- Applicative Instance
--------------------------------------------------------------------------------

instance Create (ToBinary n) =>
         Applicative (Square n) where
    pure =
        (coerce :: (Identity a -> Identity (Square n a)) -> a -> Square n a)
            create
    Square fs <*> Square xs = Square (go fs xs)
      where
        go
            :: forall m v w a b.
               (Applicative v, Applicative w)
            => Square_ m v w (a -> b) -> Square_ m v w a -> Square_ m v w b
        go (Zero ly vx) (Zero _ vy) = Zero ly (liftA2 (<*>) vx vy)
        go (Even f) (Even x) = Even (go f x)
        go (Odd f) (Odd x) = Odd (go f x)

--------------------------------------------------------------------------------
-- NFData
--------------------------------------------------------------------------------

instance (NFData1 v, NFData1 w) =>
         NFData1 (Square_ n v w) where
    liftRnf (r :: a -> ()) = go 0 0
      where
        go
            :: forall nn vv ww.
               (NFData1 vv, NFData1 ww)
            => Int -> Int -> Square_ nn vv ww a -> ()
        go _ n (Zero le xs) =
            foldl
                (\() (x,y) ->
                      case (getFirst #. getConst #.
                            (le x . le y) (Const #. First #. Just))
                               xs of
                          Nothing -> ()
                          Just z -> r z)
                (liftRnf (liftRnf r) xs)
                [ (i, j)
                | i <- [0 .. n - 1]
                , j <- [0 .. n - 1] ]
        go p n (Even xs) = go (p + 1) n xs
        go p n (Odd xs) = go (p + 1) (setBit n p) xs

instance (NFData1 v, NFData1 w, NFData a) =>
         NFData (Square_ n v w a) where
    rnf = rnf1

--------------------------------------------------------------------------------
-- Semiring
--------------------------------------------------------------------------------

instance (Semiring a, Creatable n, KnownNat n) =>
         Semiring (Square n a) where
    Square x' <.> Square y' = Square (go x' y')
      where
        go
            :: (Applicative v
               ,Applicative w
               ,Traversable v
               ,Traversable w
               ,Semiring a)
            => Square_ nn v w a -> Square_ nn v w a -> Square_ nn v w a
        go (Even x) (Even y) = Even (go x y)
        go (Odd x) (Odd y) = Odd (go x y)
        go (Zero lev x) (Zero _ y) = Zero lev (mulMatrix x y)
    (<+>) = liftA2 (<+>)
    one = unfold f 0
      where
        f 0 = (one, n)
        f c = (zero, c - 1)
        n = fromInteger (natVal (Proxy :: Proxy n)) :: Int
    zero = replicate zero

------------------------------------------------------------------------
-- Coercion utilities
------------------------------------------------------------------------

infixr 9 #.
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# INLINE (#.) #-}

infixr 9 .#
(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f
{-# INLINE (.#) #-}

infixl 0 #$
(#$) :: Coercible a b => (a -> b) -> a -> b
(#$) _ = coerce
{-# INLINE (#$) #-}
