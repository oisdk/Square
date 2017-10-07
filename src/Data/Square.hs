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
  ,ithRow)
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
import Data.Semiring

import Prelude hiding (replicate)

-- $setup
-- >>> :set -XDataKinds

data Binary = Z | O Binary | I Binary

type family EnclosedBy (p :: Nat) (n :: Nat) :: Nat where
    EnclosedBy p n = EnclosedBy' (CmpNat (2 ^ p) n) p n

type family EnclosedBy' (cmp :: Ordering) (p :: Nat) (n :: Nat) :: Nat where
    EnclosedBy' 'GT p n = p
    EnclosedBy' 'EQ p n = EnclosedBy (p + 1) n
    EnclosedBy' 'LT p n = EnclosedBy (p + 1) n

type family ToBinary' (b :: Binary) (p :: Nat) (n :: Nat) :: Binary where
    ToBinary' b 0 n = b
    ToBinary' b p n = ToBinary'' b (2 ^ (p - 1)) p n

type family ToBinary'' (b :: Binary) (below :: Nat) (p :: Nat) (n :: Nat) :: Binary where
    ToBinary'' b below p n = ToBinary''' b below (CmpNat n below) p n

type family ToBinary''' (b :: Binary) (below :: Nat) (curr :: Ordering) (p :: Nat) (n :: Nat) :: Binary where
    ToBinary''' b below 'GT p n = ToBinary' ('I b) (p-1) (n - below)
    ToBinary''' b below 'EQ p n = ToBinary' ('I b) (p-1) (n - below)
    ToBinary''' b below 'LT p n = ToBinary' ('O b) (p-1) n

type family ToBinary (n :: Nat) :: Binary where
    ToBinary n = ToBinary' 'Z (EnclosedBy 0 n) n

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
  Square { getSquare :: Square_ (ToBinary n) Proxy Identity a
         } deriving (Functor, Foldable, Traversable, Eq, Ord, Eq1, Ord1)

type Traversal s a = ∀ f. Applicative f => (a -> f a) -> s -> f s

data Square_ n v w a where
  Zero :: (∀ b. Int -> Traversal (v b) b) -> v (v a) -> Square_ 'Z v w a
  Even :: Square_ n          v    (Product w w) a   -> Square_ ('O n) v w a
  Odd  :: Square_ n (Product v w) (Product w w) a   -> Square_ ('I n) v w a

deriving instance (Functor v, Functor w) => Functor (Square_ n v w)
deriving instance (Foldable v, Foldable w) => Foldable (Square_ n v w)
deriving instance (Traversable v, Traversable w) => Traversable (Square_ n v w)

data TravSeq a = TravSeq

instance Functor TravSeq where
    fmap _ TravSeq = TravSeq

instance Applicative TravSeq where
    pure x = x `seq` TravSeq
    TravSeq <*> TravSeq = TravSeq
    TravSeq *> TravSeq = TravSeq
    TravSeq <* TravSeq = TravSeq

mkTravSeq :: NFData a => a -> TravSeq a
mkTravSeq x = rnf x `seq` TravSeq

instance NFData a => NFData (Square n a) where
    rnf s = case traverse mkTravSeq s of
      TravSeq -> ()

-- |
-- >>> fmap rows (fromList [1,2,3,4] :: Maybe (Square 2 Integer))
-- Just [[1,2],[3,4]]
rows :: Square n a -> [[a]]
rows = go (flip (foldr (:))) . getSquare
  where
    go
        :: (Foldable w, Foldable v, Functor v, Functor w)
        => (v a -> [a] -> [a]) -> Square_ n v w a -> [[a]]
    go f (Zero _ x) = foldr (\e a -> f e [] : a) [] x
    go f (Even s) = go f s
    go f (Odd s) = go g s
      where
        g (Pair vs ws) = f vs . flip (foldr (:)) ws

ithRow :: Int -> Traversal (Square n a) a
ithRow i fs (Square s) = fmap Square (go id fs s) where
  go :: (Traversable v, Traversable w, Applicative f) => (Square_ n v w a -> b) -> (a -> f a) -> Square_ n v w a -> f b
  go k f (Zero lev vv) = fmap (k . Zero lev) ((lev i . traverse) f vv)
  go k f (Even x) = go (k . Even) f x
  go k f (Odd x) = go (k . Odd) f x

-- |
-- >>> fmap cols (fromList [1,2,3,4] :: Maybe (Square 2 Integer))
-- Just [[1,3],[2,4]]
cols :: Square n a -> [[a]]
cols = go . getSquare
  where
    go
        :: (Foldable v, Foldable w, Applicative v, Applicative w)
        => Square_ n v w a -> [[a]]
    go (Zero _ x) =
        foldr (foldr f (const [])) (repeat []) x
    go (Even s) = go s
    go (Odd s) = go s
    f e a (x:xs) = (e:x) : a xs
    f _ _ [] = []

mulMat
    :: Semiring a
    => Square n a -> Square n a -> Square n a
mulMat (Square x') (Square y') = Square (go x' y')
  where
    go
        :: (Applicative v
           ,Applicative w
           ,Traversable v
           ,Traversable w
           ,Semiring a)
        => Square_ n v w a -> Square_ n v w a -> Square_ n v w a
    go (Even x) (Even y) = Even (go x y)
    go (Odd x) (Odd y) = Odd (go x y)
    go (Zero lev x) (Zero _ y) = Zero lev (getMatrix (Matrix x <.> Matrix y))

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
        go (Zero _ vx) (Zero ly vy) = Zero ly (liftA2 (<*>) vx vy)
        go (Even f) (Even x) = Even (go f x)
        go (Odd f) (Odd x) = Odd (go f x)

instance (Semiring a, Create (ToBinary n), KnownNat n) =>
         Semiring (Square n a) where
    (<.>) = mulMat
    (<+>) = liftA2 (<+>)
    one = unfold f 0 where
      f 0 = (one, n)
      f col = (zero, col-1)
      n = fromInteger (natVal (Proxy :: Proxy n)) :: Int
    zero = replicate zero

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
-- >    (∀ b. Int -> Traversal (v b) b)
-- > -> (∀ b. Int -> Traversal (w b) b)
-- > -> Int -> Int
--
-- building the indexing function allows for sharing between access
-- of different indices.

mkP
  :: Applicative f
  => (Product v w a -> b) -> (f a -> f (v a)) -> (f a -> f (w a)) -> f a -> f b
mkP k = (liftA2.liftA2) (\x y -> k (Pair x y))

-- | Creates a square of side length @n@ from some applicative.
--
-- >>> create (Just 'a') :: Maybe (Square 1 Char)
-- Just ["a"]
create :: (Applicative f, Creatable n) => f a -> f (Square n a)
create =
    create_ Square leE leI 0 1 (\k -> (const . pure) (k Proxy)) (fmap Identity)
{-# SPECIALIZE create
    :: Create (ToBinary n)
    => MaybeState s a
    -> MaybeState s (Square n a) #-}
{-# SPECIALIZE create
    :: Create (ToBinary n)
    => State s a
    -> State s (Square n a) #-}
{-# SPECIALIZE create
    :: Create (ToBinary n)
    => Identity a
    -> Identity (Square n a) #-}

replicate :: Creatable n => a -> Square n a
replicate x = runIdentity (create (Identity x))

unfold :: Creatable n => (b -> (a, b)) -> b -> Square n a
unfold f = evalState (create (State f))

unfoldMay :: Creatable n => (b -> Maybe (a, b)) -> b -> Maybe (Square n a)
unfoldMay f = evalMaybeState (create (MaybeState f))

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

instance Create 'Z where
    create_ k lev _ _ _ mkv _ = mkv (k . Zero lev) . mkv id
    {-# INLINE create_ #-}
    {-# SPECIALIZE create_
        :: (Square_ 'Z v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> State s b -> State s d)
        -> (forall b. State s b -> State s (w b))
        -> State s a
        -> State s c #-}

    {-# SPECIALIZE create_
        :: (Square_ 'Z v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> MaybeState s b -> MaybeState s d)
        -> (forall b. MaybeState s b -> MaybeState s (w b))
        -> MaybeState s a
        -> MaybeState s c #-}

    {-# SPECIALIZE create_
        :: (Square_ 'Z v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> Identity b -> Identity d)
        -> (forall b. Identity b -> Identity (w b))
        -> Identity a
        -> Identity c #-}

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
    {-# SPECIALIZE create_
        :: Create n
        => (Square_ ('O n) v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> State s b -> State s d)
        -> (forall b. State s b -> State s (w b))
        -> State s a
        -> State s c #-}

    {-# SPECIALIZE create_
        :: Create n
        => (Square_ ('O n) v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> MaybeState s b -> MaybeState s d)
        -> (forall b. MaybeState s b -> MaybeState s (w b))
        -> MaybeState s a
        -> MaybeState s c #-}

    {-# SPECIALIZE create_
        :: Create n
        => (Square_ ('O n) v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> Identity b -> Identity d)
        -> (forall b. Identity b -> Identity (w b))
        -> Identity a
        -> Identity c #-}

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
    {-# SPECIALIZE create_
        :: Create n
        => (Square_ ('I n) v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> State s b -> State s d)
        -> (forall b. State s b -> State s (w b))
        -> State s a
        -> State s c #-}

    {-# SPECIALIZE create_
        :: Create n
        => (Square_ ('I n) v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> MaybeState s b -> MaybeState s d)
        -> (forall b. MaybeState s b -> MaybeState s (w b))
        -> MaybeState s a
        -> MaybeState s c #-}

    {-# SPECIALIZE create_
        :: Create n
        => (Square_ ('I n) v w a -> c)
        -> (forall b. Int -> Traversal (v b) b)
        -> (forall b. Int -> Traversal (w b) b)
        -> Int
        -> Int
        -> (forall b d. (v b -> d) -> Identity b -> Identity d)
        -> (forall b. Identity b -> Identity (w b))
        -> Identity a
        -> Identity c #-}

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

ix_ :: (Int, Int) -> Traversal (Square_ n v w a) a
ix_ (i,j) (f :: a -> f a) = ix' id where
  ix' :: ∀ b n v w. (Square_ n v w a -> b) -> Square_ n v w a -> f b
  ix' k (Zero lev vv) = (k . Zero lev) <$> (lev i . lev j) f vv
  ix' k (Even      m) = ix' (k . Even) m
  ix' k (Odd       m) = ix' (k . Odd) m

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
  showsPrec n = showsPrec n . rows

------------------------------------------------------------------------
-- fromList
------------------------------------------------------------------------

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

fromList :: Creatable n => [a] -> Maybe (Square n a)
fromList = unfoldMay uncons' where
  uncons' [] = Nothing
  uncons' (x:xs) = Just (x,xs)
