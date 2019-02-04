{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module State where

import Prelude hiding ((++), const, max)
import ProofCombinators

-- | A Generic "State"
data GState k v = GState 
  { sVals :: [(k, v)] -- ^ binders and their values
  , sDef  :: v        -- ^ default value (for missing binder)
  }  

{-@ reflect init @-}
init :: v -> GState k v
init def = GState [] def 

{-@ reflect set @-}
set :: GState k v -> k -> v -> GState k v 
set (GState kvs v0) k v = GState ((k,v) : kvs) v0 

{-@ reflect getDefault @-}
getDefault :: (Eq k) => v -> k -> [(k, v)] -> v
getDefault v0 key ((k, v) : kvs) 
  | key == k          = v 
  | otherwise         = getDefault v0 key kvs 
getDefault v0 _ [] = v0 

{-@ reflect get @-}
get :: (Eq k) => GState k v -> k -> v 
-- get (GState kvs v0) key = getDefault v0 key kvs
get (GState []          v0) key = v0
get (GState ((k,v):kvs) v0) key = if key == k then v else get (GState kvs v0) key

{-@ lemma_get_set :: k:_ -> v:_ -> s:_ -> { get (set s k v) k == v }  @-}
lemma_get_set :: k -> v -> GState k v -> Proof 
lemma_get_set _ _ _ = () 

{-@ lemma_get_not_set :: k0:_ -> k:{k /= k0} -> val:_ -> s:_ 
                      -> { get (set s k val) k0 = get s k0 }  @-}
lemma_get_not_set :: k -> k -> v -> GState k v -> Proof 
lemma_get_not_set _ _ _ (GState {}) = ()
