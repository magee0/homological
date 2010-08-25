module TwoObjectsOneArrow where

data A -- use these as objects in the category with one non id arrow and 2 objects
data B

data TwoObjectsOneArrow :: * -> * -> * where
  IdA :: TwoObjectsOneArrow A A
  IdB :: TwoObjectsOneArrow B B
  AB  :: TwoObjectsOneArrow A B

instance C.Category TwoObjectsOneArrow where
  
  data C.Obj TwoObjectsOneArrow a where
    A0 :: C.Obj TwoObjectsOneArrow A
    B0 :: C.Obj TwoObjectsOneArrow B
    
  tgt IdA = A0
  tgt IdB = B0
  tgt AB  = B0

  src IdA = A0
  src IdB = B0
  src AB  = A0 

  id A0 = IdA
  id B0 = IdB

  IdB . AB  = AB
  AB . IdA  = AB
  IdA . IdA = IdA
  IdB . IdB = IdB  
  _ . _ = undefined -- shouldn't happen
  
-- functor from category with one non trivial arrow
-- to given category, such that the image of the arrow
-- is the given arrow in the category
data OneArrowFunctor :: (* -> * -> *) -> * -> * -> * where
  OneArrowFunctor :: (C.Category (~>)) => (a ~> b) -> OneArrowFunctor (~>) a b 
  
-- the arrow will be mono iff this functor has a limit
type instance Dom (OneArrowFunctor (~>) a b) = TwoObjectsOneArrow
type instance Cod (OneArrowFunctor (~>) a b) = (~>)

-- im not sure i fully understand the significance of this at the moment
type instance OneArrowFunctor (~>) x y :% A = x
type instance OneArrowFunctor (~>) x y :% B = y 

instance Functor (OneArrowFunctor (~>) a b) where
  
  OneArrowFunctor f %% A0 = C.src f
  OneArrowFunctor f %% B0 = C.tgt f
  OneArrowFunctor f % IdA = C.id (C.src f)
  OneArrowFunctor f % AB  = f -- this is the key part of this declaration   
  OneArrowFunctor f % IdB = C.id (C.tgt f)