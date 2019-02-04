{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--diff"       @-}
{-@ LIQUID "--ple-local"  @-}
{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Inductive where

import           Prelude hiding ((++)) 
import           ProofCombinators 
import           Peano 
import           Expressions 
import           Lists 
import qualified State as S 

--------------------------------------------------------------------------------
-- | Section 4.5.1 IndEven
--------------------------------------------------------------------------------

-- | The Prop describing an Even number 

data EvP where
  Ev :: Peano -> EvP

-- | The Predicate describing the closure of a relation 
data Ev where
  EvZ :: Ev 
  EvS :: Peano -> Ev -> Ev 

{-@ data Ev [evNat] where
      EvZ :: Prop (Ev Z) 
    | EvS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n))) 
  @-}

{-@ measure evNat @-}
{-@ evNat      :: Ev -> Nat @-}
evNat          :: Ev -> Int 
evNat EvZ       = 0 
evNat (EvS _ p) = 1 + evNat p 

--------------------------------------------------------------------------------

{-@ reflect evn @-}
evn :: Peano -> Bool 
evn Z         = True 
evn (S Z)     = False 
evn (S (S n)) = evn n

{-@ ple lemma_ev @-}
{-@ lemma_ev :: n:_ -> Prop (Ev n) -> {evn n} @-} 
lemma_ev :: Peano -> Ev -> Proof 
lemma_ev Z         _          = () 
lemma_ev (S Z)     EvZ        = () 
lemma_ev (S Z)     (EvS _ _)  = () 
lemma_ev (S (S n)) (EvS _ pn) = lemma_ev n pn  

{-@ ple lemma_evn @-}
{-@ lemma_evn :: n:{_ | evn n} -> Prop (Ev n) @-}
lemma_evn :: Peano -> Ev 
lemma_evn Z         = EvZ 
lemma_evn (S (S n)) = EvS n (lemma_evn n)

--------------------------------------------------------------------------------
-- | Section 4.5.2 IndStar
--------------------------------------------------------------------------------

-- Relations
type Rel a = a -> a -> Bool

-- | The Prop describing the closure of a relation 

data StarP a where
  Star :: Rel a -> a -> a -> StarP a

-- | The Predicate describing the closure of a relation 
data Star a where
  Refl :: Rel a -> a -> Star a
  Step :: Rel a -> a -> a -> a -> Star a -> Star a

{-@ data Star [starNat] a where
      Refl :: r:Rel a -> x:a -> Prop (Star r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Star r y z) -> Prop (Star r x z)
  @-}

{-@ measure starNat          @-}
{-@ starNat :: Star a -> Nat @-}
starNat :: Star a -> Int
starNat (Refl _ _)       = 0
starNat (Step _ _ _ _ s) = 1 + starNat s
--------------------------------------------------------------------------------

{-@ lemma_star_trans :: r:Rel a -> x:a -> y:a -> z:a
      -> Prop (Star r x y)
      -> Prop (Star r y z)
      -> Prop (Star r x z)
  @-}
lemma_star_trans :: Rel a -> a -> a -> a -> Star a -> Star a -> Star a
lemma_star_trans r x y z (Refl _ _)          yz = yz
lemma_star_trans r x y z (Step _ _ x1 _ x1y) yz = Step r x x1 z (lemma_star_trans r x1 y z x1y yz)

--------------------------------------------------------------------------------
-- | The Prop declaring the Palindrome predicate 
data PalP a where
  Pal :: [a] -> PalP a

-- | The Predicate implementing the Palindrom predicate 
data Pal a where
  Pal0 :: Pal a 
  Pal1 :: a -> Pal a 
  Pals :: a -> [a] -> Pal a -> Pal a 

{-@ data Pal [palNat] a where
      Pal0 :: Prop (Pal []) 
    | Pal1 :: x:_ -> Prop (Pal (single x)) 
    | Pals :: x:_ -> xs:_ -> Prop (Pal xs) -> Prop (Pal (mkPal x xs)) 
  @-}

{-@ reflect single @-}
single :: a -> [a]
single x = [x]

{-@ reflect mkPal @-}
mkPal :: a -> [a] -> [a]
mkPal x xs = x : (xs ++ [x])

{-@ measure palNat         @-}
{-@ palNat :: Pal a -> Nat @-}
palNat :: Pal a -> Int
palNat (Pal0 {})    = 0
palNat (Pal1 {})    = 0
palNat (Pals _ _ p) = 1 + palNat p 

{-@ ple lemma_pal @-}
{-@ lemma_pal :: xs:_ -> p:Prop (Pal xs) -> { xs = rev xs } / [palNat p] @-}
lemma_pal :: [a] -> Pal a -> Proof
lemma_pal []  (Pal0)   = () 
lemma_pal [_] (Pal1 _) = ()     
lemma_pal xs  (Pals y ys pys) = 
   --  rev xs 
  -- === rev (mkPal y ys)
  -- === rev (y : (ys ++ [y])) 
  -- ===
    (rev (ys ++ [y]))  ++ [y]      -
    ? lemma_rev_app ys [y] 
  -- === ([y] ++ rev ys) ++ [y]
    ? lemma_pal ys pys
  -- === xs 
    *** QED 


-- zoo :: xs:_ -> y:_ -> ys:_ ->  
--------------------------------------------------------------------------------
-- | The Prop declaring the AVal predicate 
data AvalP where
  Aval :: State -> AExp -> Val -> AvalP 

-- | The Predicate implementing the Palindrom predicate 
data Aval where
  AvalN :: State -> Val   -> Aval 
  AvalV :: State -> Vname -> Aval 
  AvalP :: State -> AExp -> Val -> AExp -> Val -> Aval -> Aval -> Aval 

{-@ data Aval [avalNat] where
      AvalN :: s:_ -> n:_ -> Prop (Aval s (N n) n) 
    | AvalV :: s:_ -> x:_ -> Prop (Aval s (V x) (S.get s x)) 
    | AvalP :: s:_ -> a1:_ -> v1:_ -> a2:_ -> v2:_ 
            -> Prop (Aval s a1 v1) 
            -> Prop (Aval s a2 v2)
            -> Prop (Aval s (Plus a1 a2) (add v1 v2))
  @-}

{-@ reflect add @-}
add :: Val -> Val -> Val
add x y = x + y

{-@ measure avalNat @-}
{-@ avalNat :: Aval -> Nat @-}
avalNat :: Aval -> Int
avalNat (AvalN {})              = 0
avalNat (AvalV {})              = 0
avalNat (AvalP _ _ _ _ _ p1 p2) = 1 + avalNat p1 + avalNat p2 

{-@ ple lem_aval_1 @-}
{-@ lem_aval_1 :: s:_ -> a:_ -> n:_ -> Prop (Aval s a n) -> { aval a s = n} @-}
lem_aval_1 :: State -> AExp -> Val -> Aval -> Proof 
lem_aval_1 _ (N _) n (AvalN {}) 
  = () 
lem_aval_1 s (V x) v (AvalV {}) 
  = () 
lem_aval_1 s (Plus a1 a2) v (AvalP _ _ v1 _ v2 p1 p2) 
  =   lem_aval_1 s a1 v1 p1 
  &&& lem_aval_1 s a2 v2 p2 


{-@ ple lem_aval_2 @-}
{-@ lem_aval_2 :: s:_ -> a:_ -> Prop (Aval s a (aval a s)) @-}
lem_aval_2 :: State -> AExp -> Aval 
lem_aval_2 s (N n)        = AvalN s n 
lem_aval_2 s (V x)        = AvalV s x 
lem_aval_2 s (Plus a1 a2) = AvalP s a1 v1 a2 v2 p1 p2 
  where 
    v1                    = aval a1 s
    v2                    = aval a2 s 
    p1                    = lem_aval_2 s a1
    p2                    = lem_aval_2 s a2 
