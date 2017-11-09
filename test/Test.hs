{-# OPTIONS -fplugin=AssertExplainer #-}
{-# OPTIONS -dcore-lint #-}


module Main where

import AssertExplainer (assert)

main = do
  x <- return True
  y <- return False
  assert (not x && not (not y))

{-
Assertion failed!
x = True
y = False
-}
