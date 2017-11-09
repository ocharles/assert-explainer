{-# OPTIONS -fplugin=AssertExplainer #-}
{-# OPTIONS -dcore-lint -fforce-recomp #-}

module Main where

import AssertExplainer (assert)

main = do
  x <- return True
  y <- return False
  assert (not x && not (not y) && z)
  where z = True

{-
Assertion failed!
x = True
y = False
-}
