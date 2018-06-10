{-# OPTIONS -fplugin=AssertExplainer #-}

module Test where

import Data.Char ( toUpper )

import Debug.Trace ( trace )

import AssertExplainer (assert)

example1 = do
  assert True

example2 =
  assert False

example3 =
  assert ( z `elem` map toUpper ( "Hi," ++ " ZuriHac!" ) )
    where z = 'z'

