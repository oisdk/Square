{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import           Criterion.Main
import           Data.Square

import           System.Random

import           Data.Foldable
import           Data.Maybe
import           Data.Semiring

import           Data.Proxy
import           GHC.TypeLits

import           Prelude        hiding (replicate)

integer :: IO Int
integer = randomIO

fromList' :: Creatable n => Proxy n -> [a] -> Square n a
fromList' _ xs = fromMaybe (error "fromList' supplied a list which was too small") (fromList xs)

fromListAtSize :: (KnownNat n, Creatable n) => Proxy n -> Benchmark
fromListAtSize p = bench (show (natVal p)) $ nf (sum' . fromList' p) ([1..] :: [Int])

sum' :: Square n Int -> Int
sum' = foldl' (+) 0

onesAtSize :: (KnownNat n, Creatable n) => Proxy n -> Benchmark
onesAtSize (p :: Proxy n) =
    bench (show (natVal p)) $ nf sum' (one :: Square n Int)

replicateAtSize :: (KnownNat n, Creatable n) => Proxy n -> Benchmark
replicateAtSize (p :: Proxy n) =
    bench (show (natVal p)) $ nf sum' (replicate 5 :: Square n Int)

main :: IO ()
main =
    defaultMain
        [ bgroup
              "fromList"
              [ fromListAtSize (Proxy :: Proxy 600)
              , fromListAtSize (Proxy :: Proxy 1000)]
        , bgroup
              "ones"
              [ onesAtSize (Proxy :: Proxy 600)
              , onesAtSize (Proxy :: Proxy 1000)]
        , bgroup
              "replicate"
              [ replicateAtSize (Proxy :: Proxy 600)
              , replicateAtSize (Proxy :: Proxy 1000)]
        , env (create integer :: IO (Square 1500 Int)) $
          \xs ->
               bgroup
                   "150"
                   [ bench "fmap" $ nf (fmap succ) xs
                   , bench "sum" $ nf (foldl' (+) 0) xs
                   , bench "indexing" $
                     nf
                         (\s ->
                               foldl'
                                   (+)
                                   0
                                   [ x
                                   | i <- [0 .. 1499]
                                   , j <- [0 .. 1499]
                                   , Just x <- pure (s ! (i, j)) ])
                         xs]]
