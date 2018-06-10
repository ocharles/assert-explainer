{-# OPTIONS -fplugin=AssertExplainer #-}

module Main where

import Data.Char ( toUpper )

import Debug.Trace ( trace )

import AssertExplainer (assert)

main = do
  x <- return True
  y <- return False
  n <- return 41
  assert False
  assert True
  assert ( 'z' `elem` map toUpper "Hi, ZuriHac!" )
  return () 
      
  where z = True

