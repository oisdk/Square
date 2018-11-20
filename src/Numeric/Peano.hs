{-# LANGUAGE UndecidableInstances #-}

module Numeric.Peano where

import GHC.TypeLits

data ℕ = Z | S ℕ

type family PeanoToNat' (i :: Nat) (n :: ℕ) :: Nat where
    PeanoToNat' i 'Z = i
    PeanoToNat' i ('S n) = PeanoToNat' (1 + i) n

type PeanoToNat n = PeanoToNat' 0 n
