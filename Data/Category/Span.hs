{-# LANGUAGE GADTs,
             EmptyDataDecls,
             KindSignatures,
             TypeFamilies,
             TypeOperators,
             ScopedTypeVariables             #-}
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
  Lambda(..),
  
  -- * Functors
  CospanFunctor(..)
) where

import qualified Data.Category as C
import Data.Category.Functor
import qualified Prelude

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
  IdPlusOne . IdPlusOne     = IdPlusOne
  IdMinusOne . IdMinusOne   = IdMinusOne
  ZeroMinusOne . IdZero     = ZeroMinusOne
  ZeroPlusOne . IdZero      = ZeroPlusOne
  IdPlusOne . ZeroPlusOne   = ZeroPlusOne 
  IdMinusOne . ZeroMinusOne = ZeroMinusOne
  _ . _ = Prelude.undefined -- this shouldn't happen
  
-- | The opposite category, which will allow us to define cospans.
-- I've realized this directly as I had some troubles defining a concrete
-- functor from the opposite category (defined as an opposite) into a given category
-- which suggests to me that either a) I am doing something wrong b) there is something
-- wrong with the way in which the opposite category is defined wrt the limits of ghc or
-- c) there is something wrong with the interaction of the ghc extensions I am using in
-- this particular obscure usecase. 
data LambdaOp :: * -> * -> * where
  MinusOneZero   :: LambdaOp MOne Z
  PlusOneZero    :: LambdaOp POne Z
  IdMinusOneOp   :: LambdaOp MOne MOne
  IdPlusOneOp    :: LambdaOp POne POne
  IdZeroOp       :: LambdaOp Z Z   
  
instance C.Category LambdaOp where

  data C.Obj LambdaOp a where
    MinusOneOp :: C.Obj LambdaOp MOne
    PlusOneOp  :: C.Obj LambdaOp POne
    ZeroOp     :: C.Obj LambdaOp Z
  
  tgt MinusOneZero   = ZeroOp
  tgt PlusOneZero    = ZeroOp
  tgt IdMinusOneOp   = MinusOneOp  
  tgt IdPlusOneOp    = PlusOneOp  
  tgt IdZeroOp       = ZeroOp
  
  src MinusOneZero   = MinusOneOp
  src PlusOneZero    = PlusOneOp
  src IdMinusOneOp   = MinusOneOp  
  src IdPlusOneOp    = PlusOneOp  
  src IdZeroOp       = ZeroOp
  
  id MinusOneOp      = IdMinusOneOp
  id PlusOneOp       = IdPlusOneOp
  id ZeroOp          = IdZeroOp
  
  IdZeroOp . IdZeroOp            = IdZeroOp
  IdMinusOneOp . IdMinusOneOp    = IdMinusOneOp
  IdPlusOneOp . IdPlusOneOp      = IdPlusOneOp
  IdZeroOp . MinusOneZero        = MinusOneZero
  IdZeroOp . PlusOneZero         = PlusOneZero
  PlusOneZero . IdPlusOneOp      = PlusOneZero 
  MinusOneZero . IdMinusOneOp    = MinusOneZero
  _ . _ = Prelude.undefined -- this shouldn't happen  
  
-- | Realize a functor into an abstract category
data SpanFunctor :: (* -> * -> *) -> * -> * -> * -> * where
  SpanF :: (C.Category (~>)) => (b ~> a) -> (b ~> c) -> SpanFunctor (~>) a b c
  
type instance Dom (SpanFunctor (~>) a b c) = Lambda
type instance Cod (SpanFunctor (~>) a b c) = (~>)

type instance SpanFunctor (~>) a b c :% MOne = a
type instance SpanFunctor (~>) a b c :% Z    = b
type instance SpanFunctor (~>) a b c :% POne = c

instance Functor (SpanFunctor (~>) a b c) where

  SpanF ba bc %% MinusOne    = C.tgt ba -- aka a
  SpanF ba bc %% Zero        = C.src ba -- or C.src bc
  SpanF ba bc %% PlusOne     = C.tgt bc -- aka c
  SpanF ba bc % IdMinusOne   = C.id (C.tgt ba)
  SpanF ba bc % IdPlusOne    = C.id (C.tgt bc)
  SpanF ba bc % IdZero       = C.id (C.src ba)
  SpanF ba bc % ZeroMinusOne = ba
  SpanF ba bc % ZeroPlusOne  = bc
  
-- | Realize cospan as a functor from opposite category to abstract category
-- maybe there is a slicker way to do this with the Op acting on the
-- span functor.
data CospanFunctor :: (* -> * -> *) -> * -> * -> * -> * where
  CospanF :: (C.Category (~>)) => (a ~> b) -> (c ~> b) -> CospanFunctor (~>) a b c

type instance Dom (CospanFunctor (~>) a b c) = LambdaOp
type instance Cod (CospanFunctor (~>) a b c) = (~>)

type instance CospanFunctor (~>) a b c :% MOne = a
type instance CospanFunctor (~>) a b c :% Z    = b
type instance CospanFunctor (~>) a b c :% POne = c

instance Functor (CospanFunctor (~>) a b c) where

  CospanF ab cb %% MinusOneOp       = C.src ab -- aka a
  CospanF ab cb %% ZeroOp           = C.tgt ab -- or C.tgt cb
  CospanF ab cb %% PlusOneOp        = C.src cb -- aka c
  CospanF ab cb %  IdMinusOneOp     = (C.id (C.src ab))
  CospanF ab cb %  IdPlusOneOp      = (C.id (C.src cb))
  CospanF ab cb %  IdZeroOp         = (C.id (C.tgt cb))
  CospanF ab cb %  MinusOneZero     = ab
  CospanF ab cb %  PlusOneZero      = cb


  
  
  
  
  
  
  