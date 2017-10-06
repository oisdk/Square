{-# LANGUAGE DataKinds, TypeApplications #-}

module Main (main) where

import           Criterion.Main
import           Data.Square
-- import           System.Random
-- import           Control.Monad

import Data.Foldable
import Data.Semiring

main :: IO ()
main =
    defaultMain
        [ bgroup "fromList"
          [ bench "60" $ nf (maybe [] toList . fromList @ 60) ([1..] :: [Int])
          , bench "100" $ nf (maybe [] toList . fromList @ 100) ([1..] :: [Int])
          ]
        , bgroup "ones"
          [ bench "60" $ nf (\() -> toList (one :: Square 60 Int)) ()
          , bench "100" $ nf (\() -> toList (one :: Square 100 Int)) ()
          ]
        ]

