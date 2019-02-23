{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_22 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
import           Expressions hiding (And)
import           Imp 
import 	         BigStep

-- (c1; c2) ; c3          ======      c1; (c2; c3)


{-@ lem_semi :: c1:_ -> c2:_ -> c3:_ -> s:_ -> s3:_
      -> Prop (BStep (Seq (Seq c1 c2) c3) s s3)
      -> Prop (BStep (Seq c1 (Seq c2 c3)) s s3) 
  @-}
lem_semi :: Com -> Com -> Com -> State -> State -> BStep -> BStep  
lem_semi c1 c2 c3 s s3 (BSeq c1c2 _c3 _s s2 _s3 (BSeq _c1 _c2 __s s1 _s2 c1_s_s1 c2_s1_s2) c3_s2_s3) 
  = BSeq c1 (Seq c2 c3) s s1 s3  c1_s_s1 (BSeq c2 c3 s1 s2 s3 c2_s1_s2 c3_s2_s3)


{- 

                           "c2_s1_s2"         "c3_s2_s3"
                           --------------     --------------
        "c1_s_s1"          BStep c2 s1 s2     BStep c3 s2 s3
        -------------      --------------------------------- [BSeq]
        BStep c1 s s1      BStep (c2;c3) s1 s3
        --------------------------------------- [BSeq]
        BStep (c1; (c2; c3)) s s3
       
-}        

{-@ lem_semi' :: c1:_ -> c2:_ -> c3:_ -> s:_ -> s3:_
      -> Prop (BStep (Seq c1 (Seq c2 c3)) s s3) 
      -> Prop (BStep (Seq (Seq c1 c2) c3) s s3)
  @-}
lem_semi' :: Com -> Com -> Com -> State -> State -> BStep -> BStep  
lem_semi' c1 c2 c3 s s3 (BSeq _ c2c3 _ s1 _ c1_s_s1 (BSeq _ _ _ s2 _ c2_s1_s2 c3_s2_s3)) 
  = BSeq (Seq c1 c2) c3 s s2 s3 (BSeq c1 c2 s s1 s2 c1_s_s1 c2_s1_s2) c3_s2_s3
 
{- 

        "c1_s_s1"  "c2_s1_s2"
                                        "c3_s2_s3"
        --------   --------- [BSeq]    --------------
        BStep (c1; c2) s s2             BStep c3 s2 s3
        ---------------------------------------------- [BSeq]
        BStep ((c1;c2);c3) s s3
       
-}        

-------------------------------------------------------------------------------
-- | We say `Equiv c1 c2` or `c1` is equivalent to `c2` if `c1 Sim c2` and `c2 Sim c1` 
-------------------------------------------------------------------------------

-- forall x. foo(x)
-- x:_ -> foo(x)

-- while False c == SKIP 
{-@ lem_while_false_skip :: c:Com -> Sim (While ff c) Skip @-}
lem_while_false_skip :: Com -> SimT
lem_while_false_skip c = \s t (BWhileF {}) ->  BSkip s 


{-@ lem_while_false_skip' :: c:Com -> Sim Skip (While ff c) @-}
lem_while_false_skip' :: Com -> SimT
lem_while_false_skip' c = \s t (BSkip {}) -> BWhileF ff c s

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
