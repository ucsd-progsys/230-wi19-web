{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_25 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
import           Expressions hiding (And)
import           Imp 
import 	         BigStep

-------------------------------------------------------------------------------
{- | Here are various other fun equivalences you can try to prove 
-------------------------------------------------------------------------------

	x := x		~ 	SKIP 

	x := n;		~ 	y := n
	y := n			y := n 

	x := a;		~	x := a		if x not in a  
	y := a			y := x

	IF true  c1 c2	~ 	c1 

	IF false c1 c2	~ 	c2 

	WHILE false c	~	SKIP 

	SKIP; c		~	c 

 -}


{-@ thm_bigstep_det 
      :: s:_ -> t1:_ -> t2:_ -> c:_
      -> Prop (BStep c s t1) 
      -> Prop (BStep c s t2) 
      -> { t1 == t2 }
  @-}
thm_bigstep_det :: State -> State -> State -> Com -> BStep -> BStep -> Proof
thm_bigstep_det s t1 t2 Skip (BSkip {}) (BSkip {}) 
  = () -- t1 == t2 == s 

thm_bigstep_det s t1 t2 (Assign x a) (BAssign {}) (BAssign {}) 
  = () -- t1 == t2 == asgn x a s

thm_bigstep_det s t1 t2 (Seq cA cB) 
  (BSeq _ _ _ sA1 _ cA_s_sA1 cB_sA1_t1)
  (BSeq _ _ _ sA2 _ cA_s_sA2 cB_sA2_t2)
  = thm_bigstep_det sAB1 t1 t2 cB cB_sA1_t1 cB_sA2_t2
  where
    sAB1 = sA1 ? thm_bigstep_det s sA1 sA2 cA cA_s_sA1 cA_s_sA2 

thm_bigstep_det s t1 t2 (If b c _)
  (BIfT _ _ _ _ _ c_s_t1) 
  (BIfT _ _ _ _ _ c_s_t2) 
  = thm_bigstep_det s t1 t2 c c_s_t1 c_s_t2
  
thm_bigstep_det s t1 t2 (If b _ c)
  (BIfF _ _ _ _ _ c_s_t1) 
  (BIfF _ _ _ _ _ c_s_t2) 
  = thm_bigstep_det s t1 t2 c c_s_t1 c_s_t2
  
thm_bigstep_det s t1 t2 (While b c) c_s_t1 c_s_t2 
  = undefined  
