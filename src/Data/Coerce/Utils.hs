module Data.Coerce.Utils where

import Data.Coerce

infixr 9 #.
infixl 8 .#

(#.) :: forall a b c. Coercible c b => (b -> c) -> (a -> b) -> (a -> c)
(#.) _ = coerce
{-# INLINE (.#) #-}

(.#) :: forall a b c. Coercible b a => (b -> c) -> (a -> b) -> (a -> c)
(.#) pbc _ = coerce pbc
{-# INLINE (#.) #-}
