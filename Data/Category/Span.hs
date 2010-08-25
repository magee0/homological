{-# LANGUAGE GADTs,
             EmptyDataDecls,
             KindSignatures,
             TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Span
-- Copyright   :  (c) Michael Magee 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  michaelrmagee@googlemail.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Span (

  -- * Categories
  Lambda(..)
) where

import qualified Data.Category as C

-- | Type representing minus one.
data MOne
-- | Type representing zero.
data Z
-- | Type representing plus one.
data POne  

-- | This category defines the diagram shape for a span, i.e. it has the form
-- @-1 \<- 0 -> +1@. Functors from @Lambda@ into C are spans in C
-- and similarly functors from @Op (Lambda)@ into C are cospans.
data Lambda :: * -> * -> * where
  ZeroMinusOne :: Lambda Z MOne
  ZeroPlusOne  :: Lambda Z POne
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
  IdPlusOne . ZeroPlusOne   = ZeroPlusOne 
  IdMinusOne . ZeroMinusOne = ZeroMinusOne
  _ . _ = undefined -- this shouldn't happen