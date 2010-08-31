{-# LANGUAGE GADTs,
             EmptyDataDecls,
             KindSignatures,
             TypeFamilies,
             TypeSynonymInstances,
             FlexibleInstances,
             MultiParamTypeClasses,
             TypeOperators,
			 FlexibleContexts,
			 UndecidableInstances,
			 ScopedTypeVariables
              #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Abelian.AbelianGroups
-- Copyright   :  (c) Michael Magee 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  michaelrmagee@googlemail.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------                
module Data.Category.Abelian.AbelianGroups where

import qualified Data.Category as C
import qualified Data.Category.Functor as F
import qualified Data.Category.Unit as U
import qualified Data.Category.Abelian as A
import qualified Data.Category.Span as S
import Prelude (($), Bool, Eq, undefined, (==))
import Data.Bool
import qualified Prelude

-- | Redefinition of this class as I don't want to refer to mappend or 
-- have 'concat' present in what follows.
class  Monoid m where
  (<*>) :: m -> m -> m
  idd   :: m

-- | A group is a monod with inverses.  
class Monoid g => Group g where
  inv :: g -> g
  
-- | Refinement type for abelian groups.  
class Group g => AbGrp g -- may need to include details to enforce an abelian category 

-- | Maps a monoid to the corresponding one object category.
data Arrowized m a b where
  Arrowize :: Monoid m => m -> Arrowized m m m 

instance Eq m => Eq (Arrowized m a b) where
  Arrowize m1 == Arrowize m2 = m1 == m2  
  
-- | Declaration that the 'arrowized' data type is indeed a category.  
instance Monoid m => C.Category (Arrowized m) where
  
  data C.Obj (Arrowized m) a where -- one object category
     MonoidO :: C.Obj (Arrowized m) m
  
  src (Arrowize _) = MonoidO
  tgt (Arrowize _) = MonoidO
  
  id MonoidO                    = Arrowize idd
  (Arrowize a) . (Arrowize b) = Arrowize $ a <*> b

-- | Lifts the identity up to the arrows from the monoid.
idA :: (Monoid m) => (Arrowized m m m)
idA = Arrowize idd

-- | Lifts the groups invert to the arrows.  
invA :: (Group m) => (Arrowized m m m) -> (Arrowized m m m)
invA (Arrowize mObj) = Arrowize (inv mObj) 

-- | The trivial group. Non empty for posterity.  
data TrivialGroup = TGM 

instance Eq TrivialGroup where
 TGM == TGM = True

-- | Description of how it becomes a monoid.
instance Monoid TrivialGroup where
  TGM <*> TGM = TGM
  idd = TGM
  
-- | Inverse of only element is only element.  
instance Group TrivialGroup where  
  inv TGM = TGM  
 
-- | It is also an abelian group. 
instance AbGrp TrivialGroup 

-- The booleans form a monoid.
instance Monoid Bool where 
  (<*>) = (&&)
  idd   = True

-- | A functor from the unit category to one element.
data UnitDiagram :: (* -> * -> *) -> * -> * where
  UD :: (C.Category (~>)) => (C.Obj (~>) a) -> UnitDiagram (~>) a
  
-- | The domain of the unit diagram is the arrowization of the trivial group.
type instance F.Dom (UnitDiagram (~>) a) = (Arrowized TrivialGroup)
-- | The codomain is the category bound by the type parameter.
type instance F.Cod (UnitDiagram (~>) a) = (~>)
-- | The image object-type is bound by the second type parameter.
type instance (UnitDiagram (~>) a) F.:% TrivialGroup = a

-- | For each abelian group there is a morphism from
-- the unit group to this group, or a functor between their arrowizations.
instance (AbGrp g) => F.Functor (UnitDiagram (Arrowized g) a) where
  (UD MonoidO) %% MonoidO     = MonoidO
  (UD MonoidO) % (Arrowize _) = Arrowize (idd)

-- | This data type is constructed from functors between the arrowizations of
-- the two groups in question.  
data AbGrps :: * -> * -> * where 
  AbGrpsA :: (F.Functor ftag, AbGrp g, AbGrp h, (Arrowized g) ~ (F.Dom ftag), (Arrowized h) ~ (F.Cod ftag)) => 
    ftag -> AbGrps (F.CatW (Arrowized g)) (F.CatW (Arrowized h))
  
instance C.Category AbGrps where

  data C.Obj AbGrps a where -- objects are wrapped categories
    AbGrpsO :: AbGrp g => C.Obj AbGrps (F.CatW (Arrowized g))
    
  src (AbGrpsA _) = AbGrpsO 
  tgt (AbGrpsA _) = AbGrpsO
  
  id AbGrpsO = AbGrpsA (F.Id)
  AbGrpsA hom' . AbGrpsA hom = AbGrpsA (hom' F.:.: hom) 

-- | The zero object is supplied by the wrapped, arrowized version of
-- the trivial group. There is only one type for the 'other level'
-- version of the zero object. We use the functor-to-morphism map to
-- realize termination as a constant functor to the arrowized trivial
-- group and initialization as the 'unit diagram'. 
instance A.HasZeroObject AbGrps where
    type A.ZeroObject AbGrps = F.CatW (Arrowized TrivialGroup) 
    zeroObject                = AbGrpsO
    initialize AbGrpsO        = AbGrpsA (UD MonoidO)
    terminate  AbGrpsO        = AbGrpsA $ F.Const MonoidO

  
data Product :: * -> * -> * where
  Prod :: a -> b -> Product a b deriving Eq

-- | A product inherits a monoid structure.  
instance (Monoid a, Monoid b) => Monoid (Product a b) where
  (Prod x y) <*> (Prod x' y') = Prod (x <*> x') (y <*> y')
  idd = Prod idd idd

prodF :: (a -> c) -> (b -> d) -> Product a b -> Product c d 
prodF f g (Prod x y) = Prod (f x) (g y)


-- a new start, maybe easier?   
data AGHom :: * -> * -> * where   
  Mdrop :: (AbGrp m, AbGrp n, F.Functor f, F.Dom f ~ Arrowized m, F.Cod f ~ Arrowized n) =>  f -> AGHom m n -- and moreover this will be be an arrow in the category if the functor contract obeyed    

	
instance C.Category AGHom where

  data C.Obj AGHom a where -- objects are the groups
    AbGrpsOO :: AbGrp g => C.Obj AGHom g
    
  src (Mdrop _) = AbGrpsOO 
  tgt (Mdrop _) = AbGrpsOO
  
  id AbGrpsOO = Mdrop (F.Id)
  Mdrop hom' . Mdrop hom = Mdrop (hom' F.:.: hom) 

instance A.HasZeroObject AGHom where
    type A.ZeroObject AGHom    = TrivialGroup
    zeroObject                 = AbGrpsOO
    initialize AbGrpsOO        = Mdrop (UD MonoidO)
    terminate  AbGrpsOO        = Mdrop (F.Const MonoidO)  

data DiffFunctor :: * -> * -> * -> * -> * where
  DiffF :: (Group m, Group n, F.Functor f, F.Functor g, 
    F.Dom f ~ Arrowized m,  F.Dom g ~ Arrowized m, -- same domains
	F.Cod f ~ Arrowized n,  F.Cod g ~ Arrowized n) -- and codomains
	=> f -> g -> DiffFunctor f g m n
	
type instance F.Dom (DiffFunctor f g m n) = Arrowized m
type instance F.Cod (DiffFunctor f g m n) = Arrowized n

type instance (DiffFunctor f g m n) F.:% m = n

instance (Group m, Group n, F.Functor f, F.Functor g, 
    F.Dom f ~ Arrowized m,  F.Dom g ~ Arrowized m, -- same domains
	F.Cod f ~ Arrowized (f F.:% m),  F.Cod g ~ Arrowized (g F.:% m)) => F.Functor (DiffFunctor f g m n) where
	
	DiffF f g %% MonoidO = MonoidO
	DiffF f g %  arrow@(Arrowize _) = (f F.% arrow) C.. (g F.% (invA arrow)) -- i.e. (f - g) 	
	
data Kernel :: * -> * where -- the kernel of the homomorphism, parameterized by first type.
  Restrict :: a -> Kernel (a `AGHom` b)
  
-- | The kernel of a monoid morphism is a monoid, with multiplication
-- given by restriction.  
instance (Monoid a, Monoid b) => Monoid (Kernel (a `AGHom` b)) where
  idd = Restrict idd
  (Restrict x) <*> (Restrict y) = Restrict (x <*> y)   
  
data FirstProj :: * -> * where --parameters by first generic
  FirstP :: (AbGrp a) => FirstProj a -- projection out of any product
  
type instance F.Dom (FirstProj a) = Arrowized (Product a )   
type instance F.Cod (FirstProj a) = Arrowized a

type instance (FirstProj a) F.:% (Product a b) = a

instance F.Functor (FirstProj a b) where

  FirstP %% MonoidO = MonoidO -- always same underlying object
  FirstP %  arrow@(Arrowize (Prod x _)) = Arrowize x
  
	
-- | Gives the difference of two parallel arrows in an abelian group.  
--diffHomo :: a `AGHom` b -> a `AGHom` b -> a `AGHom` b


--class (AbGrp a, AbGrp b , AbGrp c) => Pullback AGHom a b c (AbPullback
  
  

-- | Show existence of pullbacks.

-- for all cospan diagrams in AbGrps build
-- a) the concrete cospan functor
-- b) the limit cone to this functor.
-- to do this we need to construct a natural transformation
-- first we need a type corresponding to the pullback

-- the pullback object corresponds to a restricted product.

--instance L.HasLimits (C.Op Lambda) AbGrps where



  --limitUniv (NatO f) = limitUniversal
    
    
    
    