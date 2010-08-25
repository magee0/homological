{-# LANGUAGE TypeOperators, 
             TypeFamilies, 
             GADTs, 
             EmptyDataDecls, 
             RankNTypes,
             FlexibleContexts,
             FlexibleInstances,
             MultiParamTypeClasses,
             FunctionalDependencies             #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Abelian
-- Copyright   :  (c) Michael Magee 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  michaelrmagee@googlemail.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------             
module Data.Category.Abelian (

  -- * Classes refining Category
  HasZeroObject,
  HasPullbacks,
  HasPushouts,
  AbelianCategory,
  
  -- * Type Families
  Monos,
  Epis,
  Kernels,
  Cokernels,
  
  -- * Miscellaneous classes
  Eql

) where

import qualified Data.Category as C
import qualified Data.Category.Void as V
import qualified Data.Category.Limit as L
import Data.Category.Functor -- need to do this to declare instance...
import Data.Category.Span
import qualified Data.Category.NaturalTransformation as N
import Prelude hiding ((.), id, Functor, product)

-- | An instance of @HasZeroObject (~>)@ gives a type for the zero object and
-- ways to terminate or initialize any object in the category.
class C.Category (~>) => HasZeroObject (~>) where
  type ZeroObject (~>) :: *
  zeroObject :: C.Obj (~>) (ZeroObject (~>))
  terminate  :: C.Obj (~>) a -> a ~> (ZeroObject (~>))
  initialize :: C.Obj (~>) a -> (ZeroObject (~>)) ~> a

-- | A pullback is the limit of a cospan, so the existence of limits implies
-- the existence of all pullbacks.
class (L.HasLimits (C.Op Lambda) (~>)) => HasPullbacks (~>)

-- | A pushout is the colimit of a span, so the existence of colimits implies the
-- existence of all pushouts.
class (L.HasColimits Lambda (~>)) => HasPushouts (~>)

-- | @Monos (~>) a b@ is all monomorphisms from a to b in ~>.
type family Monos (~>) :: * -> * -> *
-- | @Epis (~>) a b@ is all epimorphisms from a to b in ~>.
type family Epis (~>) :: * -> * -> *

-- | @Kernels (~>) a b@ is all kernels from a to b in ~>.
type family Kernels (~>) :: * -> * -> *
-- | @Cokernels (~>) a b@ is all cokernels from a to b in ~>.
type family Cokernels (~>) :: * -> * -> *

-- | @AbelianCategory (~>)@ denotes that ~> is an abelian category, and hence 
-- has 
--
--   (1)  a zero object
--
--   (2)  all pushouts and pullbacks
--
--   (3)  all monomorphisms normal and all epimorphisms conormal.
--
-- Such categories allow us to realize homology theories as derived functors.
class ( C.Category (~>), 
       HasZeroObject (~>), 
       HasPullbacks (~>), 
       HasPushouts (~>),
       Eql (Monos (~>)) (Kernels (~>)),
       Eql (Epis (~>)) (Cokernels (~>))) => AbelianCategory (~>) where
  
-- | Hack until equality in superclass constraints supported.
class Eql a b | a -> b, b -> a
instance Eql a a  
	