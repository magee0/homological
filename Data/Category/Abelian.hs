{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, EmptyDataDecls, RankNTypes #-}
module Data.Category.Abelian where

import qualified Data.Category as C
import qualified Data.Category.Void as V

-- this can maybe go somewhere else
class C.Category (~>) => HasZeroObject (~>) where
  type ZeroObject (~>) :: *
  zeroObject :: C.Obj (~>) (ZeroObject (~>))
  terminate  :: C.Obj (~>) a -> a ~> (ZeroObject (~>))
  initialize :: C.Obj (~>) a -> (ZeroObject (~>)) ~> a

-- Category to define spans and cospans 
-- (so then define pushout and pull backs as limits)
data MOne
data Z
data POne 
  
data Lambda :: * -> * -> * where
  ZeroMinusOne :: Lambda Z MOne
  ZeroPlusOne  :: Lambda Z PObne
  IdMinusOne   :: Lambda MOne MOne
  IdPlusOne    :: Lambda POne POne
  IdZero       :: Lambda Z Z
  
instance C.Category Lambda where

  data C.Obj Lambda a where
    MinusOne :: C.Obj Lambda MOne
    PlusOne  :: C.Obj Lambda POne
    Zero     :: C.Obj Lambda Z
  
  tgt ZeroMinusOne = MinusOne
  tgt ZeroPlusOne  = PlusOne
  tgt IdMinusOne   = MinusOne  
  tgt IdPlusOne    = PlusOne  
  tgt IdZero       = Zero
  
  src ZeroMinusOne = Zero
  src ZeroPlusOne  = Zero
  src IdMinusOne   = MinusOne  
  src IdPlusOne    = PlusOne  
  src IdZero       = Zero
  
  id MinusOne      = IdMinusOne
  id PlusOne       = IdPlusOne
  id Zero          = IdZero
  
  IdZero . IdZero           = IdZero
  ZeroMinusOne . IdZero     = ZeroMinusOne
  ZeroPlusOne . IdZero      = ZeroPlusOne
  IdPlusOne . ZeroPlusOne   = PlusOneZero 
  IdMinusOne . ZeroMinusOne = ZeroMinusOne
  _ . _ = undefined -- this shouldn't happen
 
  
class (HasZeroObject (~>)) => AbelianCategory (~>) where
    -- the zero element exists
    

