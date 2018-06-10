{-# OPTIONS -fplugin=AssertExplainer #-}

module Main where

import Debug.Trace ( trace )

import AssertExplainer (assert)

main = do
  x <- return True
  y <- return False
  n <- return 41
  assert False
  assert (not x && not (not y) && z && n == 42)
  return () 
      
  where z = True

