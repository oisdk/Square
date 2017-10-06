{-# LANGUAGE DataKinds, TypeApplications #-}

module Main (main) where

import           Criterion.Main
import           Data.Square
-- import           System.Random
-- import           Control.Monad

import Data.Foldable

main :: IO ()
main =
    defaultMain
        [ bgroup "fromList"
          [ bench "8" $ nf (maybe [] toList . fromList @ 8) ([1..] :: [Int])
          , bench "16" $ nf (maybe [] toList . fromList @ 16) ([1..] :: [Int])
          , bench "60" $ nf (maybe [] toList . fromList @ 60) ([1..] :: [Int])
          , bench "100" $ nf (maybe [] toList . fromList @ 100) ([1..] :: [Int])
          ]
        ]

