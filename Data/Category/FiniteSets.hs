{-# LANGUAGE GADTs,
             EmptyDataDecls,
             KindSignatures,
             TypeFamilies #-}
module Data.Category.FiniteSets where

import qualified Data.Category as C
import qualified Prelude

restrictedId :: (Finite a) => a -> a
restrictedId x = x

class Finite a where -- include any property of a finite set needed

data FinSets :: * -> * -> * where
  AnyMorphism :: (Finite a, Finite b) => (a -> b) -> FinSets a b
  Identity    :: FinSets a a -- bit of a hack at present
  
instance C.Category FinSets where
  
  data C.Obj FinSets a = HaskO
    
  tgt (AnyMorphism f) = HaskO
  tgt Identity = HaskO

  src (AnyMorphism f) = HaskO
  src Identity = HaskO

  id HaskO = Identity

  AnyMorphism f . AnyMorphism g = AnyMorphism (f Prelude.. g)
  Identity . AnyMorphism g = AnyMorphism g
  AnyMorphism g . Identity = AnyMorphism g
 
  