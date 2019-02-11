{-@ LIQUID "--reflection" @-}
{- LIQUID "--diff"       @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Inductive where

import           Prelude hiding ((++)) 
import           ProofCombinators 
import           Lists 
import           Expressions 
import qualified State as S 

--------------------------------------------------------------------------------
-- | Peano numbers
--------------------------------------------------------------------------------
data Peano = Z | S Peano

--------------------------------------------------------------------------------
-- | Defining "Even Numbers"
--------------------------------------------------------------------------------

-- | The "Prop" describing an Even number `(Ev n)`

data EvP where
  Ev :: Peano -> EvP

-- | The ways to "construct evidence" of evenness i.e. that "prove" `Ev n`

data Ev where
  EvZ :: Ev 
  EvS :: Peano -> Ev -> Ev 

{-@ data Ev where
      EvZ :: Prop (Ev Z) 
    | EvS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n))) 
  @-}

{- | Read the above as there are two "rules" to determine even-ness 

     1. 

      ------------------ [EvZ]
         Ev Z  



     2.

         Ev n
      ------------------ [EvS]
         Ev (S (S n))  


 -}


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

{-@ data Star a where
      Refl :: r:Rel a -> x:a -> Prop (Star r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Star r y z) 
           -> Prop (Star r x z)
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

{-@ data Pal a where
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
    (rev (ys ++ [y]))  ++ [y]      --
    ? lemma_rev_app ys [y] 
  -- === ([y] ++ rev ys) ++ [y]
    ? lemma_pal ys pys
  -- === xs 
    *** QED 

--------------------------------------------------------------------------------
-- | The Prop declaring the AvRel predicate 
data AvRelP where
  AvRel :: State -> AExp -> Val -> AvRelP 

-- | The Predicate implementing the Palindrom predicate 
data AvRel where
  AvRelN :: State -> Val   -> AvRel 
  AvRelV :: State -> Vname -> AvRel 
  AvRelP :: State -> AExp -> Val -> AExp -> Val -> AvRel -> AvRel -> AvRel 

{-@ data AvRel where
      AvRelN :: s:_ -> n:_ 
            -> Prop (AvRel s (N n) n) 
    | AvRelV :: s:_ -> x:_ 
            -> Prop (AvRel s (V x) (S.get s x)) 
    | AvRelP :: s:_ -> a1:_ -> v1:_ -> a2:_ -> v2:_ 
            -> Prop (AvRel s a1 v1) 
            -> Prop (AvRel s a2 v2)
            -> Prop (AvRel s (Plus a1 a2) (add v1 v2))
  @-}

{-@ lem_avrel :: s:_ -> a:_ -> n:_ -> Prop (AvRel s a n) 
              -> { n == aval a s } @-}
lem_avrel :: State -> AExp -> Val -> AvRel -> Proof 
lem_avrel s (N n)        _n (AvRelN {}) 
   = () 
lem_avrel s (V x)        _  (AvRelV {}) 
   = () 
lem_avrel s (Plus a1 a2) _  (AvRelP _s _a1 n1 _a2 n2 p_a1_n1 p_a2_n2) 
   =   lem_avrel s a1 n1 p_a1_n1 -- aval a1 s == n1 
   &&& lem_avrel s a2 n2 p_a2_n2 -- aval a2 s == n2

lem_avrel s _ _ _ = impossible "" 



-- s:_ -> a:_ -> n:{ n = aval a s } -> Prop (AvRel s a n)



{-@ reflect add @-}
add :: Val -> Val -> Val
add x y = x + y
