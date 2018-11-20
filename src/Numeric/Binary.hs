{-# LANGUAGE UndecidableInstances #-}

module Numeric.Binary where

import Numeric.Peano
import GHC.TypeLits

type family BinToNat (xs :: [ℕ]) :: Nat where
    BinToNat '[] = 0
    BinToNat (x : xs) = (2 ^ PeanoToNat x) * (1 + 2 * BinToNat xs)

type family NatToBin (n ∷ Nat) ∷ [ℕ] where
    NatToBin 0 = '[]
    NatToBin n = NatToBin' Z (Mod n 2) (Div n 2)

type family NatToBin' (i ∷ ℕ) (r ∷ Nat) (d ∷ Nat) ∷ [ℕ] where
    NatToBin' i 1 d = i : NatToBin d
    NatToBin' i 0 d = NatToBin' (S i) (Mod d 2) (Div d 2)
