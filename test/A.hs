{-# LANGUAGE GADTs, TypeFamilies, MultiParamTypeClasses, FunctionalDependencies, 
             FlexibleInstances, FlexibleContexts, UndecidableInstances,
             TypeOperators, ScopedTypeVariables, DataKinds, ConstraintKinds, 
             StandaloneDeriving, DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Data
import Data.Data.TH
import Test.Hspec
import Test.QuickCheck

data S a b where
  Sa :: S a b
  Sb :: S Int b
  Sc :: S Int Int
  Sd :: Int -> Int -> S Int Int
  Se :: a -> S a a

$(deriveDataGADT ''S)

main = hspec $ return ()