{-# LANGUAGE GADTs,
             EmptyDataDecls,
             KindSignatures,
             TypeFamilies,
             TypeSynonymInstances             #-}
module FiniteAbelianGroups where

import qualified Data.Category as C
import Data.Category.FiniteSets

class Grp g where
  mult :: g -> g -> g
  id ::   g
  inv ::  g -> g
  
class (Grp g) => AbGrp g
class (Finite g, AbGrp g) => FinAbGrp g
  

type FreeAbelian a = a -> Int
 
-- finally, an actual example 
instance Grp (FreeAbelian a) where
  mult f1 f2 x = (f1 x) + (f2 x) -- add the indices
  inv f1 x = -(f1 x)             -- negative the indices
  id x = 0
  
type family GroupHomos a b :: *
  
--class (FinAbGrp a, FinAbGrp b) => GroupHom a b where
  -- i am seriously considering representing my groups at the type level...
data FinAbGrps :: * -> * -> * where
  Homomorphisms :: (FinAbGrp a, FinAbGrp b) => GroupHomos a b -> FinAbGrps a b
  
 

--instance C.Category FinAbGrps where