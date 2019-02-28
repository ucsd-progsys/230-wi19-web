\begin{code}
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
\end{code}

------------------------------------------------------------------------------
Big Step semantics: C1: S -> S’, 

	where C1 is a   set   of commands,
	      S  is the state before executing C1,
	      S' is the state after  executing C1,

------------------------------------------------------------------------------
   A language is deterministic 
=> There is at most one final state.
=> C ( S → S’) such that S’ is unique.
=> If C : S-> S1 and C: S -> S2, then S1 = S2
=> For all C S S1 S2, BStep C S S2  →  BStep C S S1 →  S1 == S2

(Q: When can there be zero final state? Non-terminating program, e.g., While True {Skip}.)

How to Prove? Induction! Case split on Com, and match corresponding BStep with the Com. 

-------------------------------------------------------------------------------



\begin{code}
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

------
-- Seq is an interesting case:
-- C1 ; C2 
-- S -> Smid  -> Sf
-- S -> Smid’ -> Sf’
-- Make use of the middle state, and we use induction on C1 and C2
-- Namely, we need to show that sA1 == sA2 by induction on C1
-- Then, we show that t1 == t2 by induction on C2
-------
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
  = undefined  --left as homework
\end{code}


-------------------------------------------------------------------------------
{- | Here are various other fun equivalences you can try to prove 
-------------------------------------------------------------------------------

	x := x		~ 	SKIP 

	x := n;		~ 	y := n
	y := n			y := n 

	x := a;		~	x := a		if x not in a  -- necessary, eg: a = x + 1
	y := a			y := x

	IF true  c1 c2	~ 	c1 

	IF false c1 c2	~ 	c2 

	WHILE false c	~	SKIP 

	SKIP; c		~	c 

 -}

---------------------------------------

Small Step Semantics:  (C, S)   → (C’ , S’)

C is a set of commands, we want to execute the first command in C such that we get to C’ and S’

-------
Example:

S                S[x -> 0]           S[x-> 1]
x:= 0		 x:= x + 1	     y:= x
x:= x + 1;	 y:= x		     z:= y + 1  
y:= x		 z:= y + 1                      .......
z:= y+1
----------

Comparison: 

C: S_in    ->   S_out           --Big Step

(C S_in)   ->* (Skip, S_out)    --Small Step


------------

Designing rules for small step (incompleted)

---------------------
(Skip; C, S) -> (C, S)


(CA, S) -> (CA’, S’)
------------------------
(CA; CB, S) -> (CA’; CB, S’)


------------------------
(x:=a , s) → (Skip, S[x:aval a s] )


Bval b s = True
--------------------
(IF b c1 c2, s) -> (c1, s)

Bval b s = False
--------------------
(IF b c1 c2, s) -> (c2, s)



