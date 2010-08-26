{-# LANGUAGE GADTs,
             EmptyDataDecls,
             KindSignatures,
             TypeFamilies #-}
module Data.Category.FiniteSets where

import qualified Data.Category as C
import qualified Data.Category.Limit as L
import qualified Prelude

data FinSets :: * -> * -> * where -- i really need to prove that all morphisms can be built this way
  EmptyId         :: FinSets Empty Empty  -- and that they are in one to one
  ExtFirstByOther :: t -> FinSets s t -> FinSets (Another s) t -- makes the domain bigger and specifies where this new object maps
  ExtSecond       :: FinSets s t -> FinSets s (Another t) -- makes the codomain bigger

-- evaluates a function  (strange I know... thought this was part of haskell already ;)
eval :: FinSets a b -> a -> b
eval EmptyId _ = Prelude.undefined
eval (ExtFirstByOther x _) LastAdded = x -- this terminates the recursion
eval (ExtFirstByOther x hom) (Old y) = eval hom y -- this recurses
eval (ExtSecond hom) x = Old (eval hom x)
 
-- | Generates a map from the empty set to a given set. 
emptyTo :: C.Obj FinSets a -> FinSets Empty a
emptyTo Empty0 = EmptyId
emptyTo (Another0 other) = ExtSecond (emptyTo other)  

data Empty
data Another s = LastAdded | Old s -- this one is bigger!
  
instance C.Category FinSets where
  
  data C.Obj FinSets a where -- are these sets really finite?
   Empty0   :: C.Obj FinSets Empty
   Another0 :: C.Obj FinSets s -> C.Obj FinSets (Another s) 
   
  src EmptyId                 = Empty0
  src (ExtFirstByOther _ hom) = Another0 (C.src hom)  
  src (ExtSecond hom)         = C.src hom
  
  tgt EmptyId                 = Empty0
  tgt (ExtFirstByOther _ hom) = C.tgt hom  
  tgt (ExtSecond hom)         = Another0 (C.tgt hom)
  
  id Empty0               = EmptyId
  id (Another0 set)       = (ExtFirstByOther LastAdded (ExtSecond (C.id set)))
 -- id (Another0 set)      =  ExtFirstBy LastAdded (fill set (id set) (emptyTo set))-- inefficient
  
  EmptyId . EmptyId                 = EmptyId
  (ExtSecond hom) . hom'            = ExtSecond (hom C.. hom')
  hom' . (ExtFirstByOther x hom)             = ExtFirstByOther (eval hom' x) (hom' C.. hom)  
  (ExtFirstByOther _ hom') . (ExtSecond hom) = hom' C.. hom
  _ . _ = Prelude.undefined -- shouldn't happen
  
-- | The initial object in the catgeory of sets is the empty set.  
instance L.HasInitialObject FinSets where

  type L.InitialObject FinSets = Empty
  initialObject = Empty0
  initialize set = emptyTo set
  

    
 
  