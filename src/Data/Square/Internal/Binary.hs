{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Square.Internal.Binary where

import           GHC.TypeLits

-- Some type families for binary numbers. The convoluted methods are
-- because we don't have type-level division, and the hand-implemented
-- version blows the typechecker's stack with anything bigger than 200.
-- We do have type-level exponentiation, though, making these methods
-- viable.

data Binary
    = Z
    | O Binary
    | I Binary

type family EnclosedBy (p :: Nat) (n :: Nat) :: Nat where
        EnclosedBy p n = EnclosedBy' (CmpNat (2 ^ p) n) p n

type family EnclosedBy' (cmp :: Ordering) (p :: Nat) (n :: Nat) ::
     Nat where
        EnclosedBy' 'GT p n = p
        EnclosedBy' 'EQ p n = EnclosedBy (p + 1) n
        EnclosedBy' 'LT p n = EnclosedBy (p + 1) n

type family ToBinary' (b :: Binary) (p :: Nat) (n :: Nat) :: Binary
     where
        ToBinary' b 0 n = b
        ToBinary' b p n = ToBinary'' b (2 ^ (p - 1)) p n

type family ToBinary'' (b :: Binary) (below :: Nat) (p :: Nat)
     (n :: Nat) :: Binary where
        ToBinary'' b below p n = ToBinary''' b below (CmpNat n below) p n

type family ToBinary''' (b :: Binary) (below :: Nat)
     (curr :: Ordering) (p :: Nat) (n :: Nat) :: Binary where
        ToBinary''' b below 'GT p n = ToBinary' ('I b) (p - 1) (n - below)
        ToBinary''' b below 'EQ p n = ToBinary' ('I b) (p - 1) (n - below)
        ToBinary''' b below 'LT p n = ToBinary' ('O b) (p - 1) n

type family ToBinary (n :: Nat) :: Binary where
        ToBinary n = ToBinary' 'Z (EnclosedBy 0 n) n
