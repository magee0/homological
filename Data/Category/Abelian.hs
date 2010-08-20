{-# OPTIONS_GHC -XTypeOperators #-} 
module Data.Category.Abelian where

import qualified Data.Category as C
import qualified Data.Category.Void as V

class (C.Category (~>)) => HasZeroObject (~>) where
  type ZeroObject (~>) :: *
  zeroObject :: Obj ~> (ZeroObject ~>)
  terminate  :: Obj ~> a -> a ~> ZeroObject ~>
  initialize :: Obj ~> a -> InitialObject ~> ~> a

class (HasZeroObject (~>)) => AbelianCategory (~>) where
    -- the zero element exists
    

