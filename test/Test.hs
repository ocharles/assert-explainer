{-# OPTIONS -fplugin=AssertExplainer #-}

module Main where

import Data.Char ( toUpper )

import Debug.Trace ( trace )

import AssertExplainer (assert)

example1 = do
  assert True

example2 =
  assert False

example3 =
  assert ( length xs == 4 )
    where xs = [ 1, 2, 3 ]

example4 =
  assert ( z `elem` map toUpper ( "Hi," ++ " ZuriHac!" ) )
    where z = 'z'

main = do
  putStrLn "Example 1"
  example1

  example2

  example3

  example4
