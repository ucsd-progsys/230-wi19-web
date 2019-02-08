{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--diff"       @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_8 where

import           Prelude hiding ((++)) 
import           ProofCombinators 
import           Lists 
import           Expressions 
import qualified State as S 


-----------------------------------------------------------------------
-- Relations
type Rel a = a -> a -> Bool

-- | The Prop describing the closure of a relation 

data StarP a where
  Star :: Rel a -> a -> a -> StarP a

-- | The Predicate describing the closure of a relation 
data Star a where
  Refl :: Rel a -> a -> Star a
  Step :: Rel a -> a -> a -> a -> Star a -> Star a

{-@ data Star a where
      Refl :: r:Rel a -> x:a -> Prop (Star r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Star r y z) -> Prop (Star r x z)
  @-}

--------------------------------------------------------------------------------

{-@ lemma_star_trans :: r:Rel a -> x:a -> y:a -> z:a
      -> Prop (Star r x y)
      -> Prop (Star r y z)
      -> Prop (Star r x z)
  @-}
lemma_star_trans :: Rel a -> a -> a -> a -> Star a -> Star a -> Star a
lemma_star_trans = undefined






dummy :: Int
dummy = 10 
