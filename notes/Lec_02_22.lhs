\documentstyle{article}

\begin{document}

\begin{code}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}

{-# LANGUAGE GADTs #-}

module Lec_2_22 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
import           Expressions hiding (And)
import           Imp 
import 	         BigStep
\end{code}

CSE 230: Programming Languages
==============================

-----------------------------------
Friday, February 22 (Lecture 16)
-----------------------------------

\section{Big Step Semantics}

A language is syntax-directed when each semantic rule corresponds to a
specific syntactic constructor (ie: BSeq - Seq, BSkip - Skip)

\begin{code}
data BStepP where
  BStep :: Com -> State -> State -> BStepP 

data BStep where 
  BSkip   :: State -> BStep 
  BAssign :: Vname -> AExp -> State -> BStep 
  BSeq    :: Com   -> Com  -> State -> State -> State -> BStep -> BStep -> BStep 
  BIfT    :: BExp  -> Com  -> Com   -> State -> State -> BStep -> BStep  
  BIfF    :: BExp  -> Com  -> Com   -> State -> State -> BStep -> BStep
  BWhileF :: BExp  -> Com  -> State -> BStep 
  BWhileT :: BExp  -> Com  -> State -> State -> State -> BStep -> BStep -> BStep 

{-@ data BStep  where 
      BSkip   :: s:State 
              -> Prop (BStep Skip s s)
    | BAssign :: x:Vname -> a:AExp -> s:State 
              -> Prop (BStep (Assign x a) s (asgn x a s)) 
    | BSeq    :: c1:Com -> c2:Com -> s1:State -> s2:State -> s3:State 
              -> Prop (BStep c1 s1 s2) -> Prop (BStep c2 s2 s3) 
              -> Prop (BStep (Seq c1 c2) s1 s3)
    | BIfT    :: b:BExp -> c1:Com -> c2:Com -> s:{State | bval b s} -> s1:State
              -> Prop (BStep c1 s s1) -> Prop (BStep (If b c1 c2) s s1)
    | BIfF    :: b:BExp -> c1:Com -> c2:Com -> s:{State | not (bval b s)} -> s2:State
              -> Prop (BStep c2 s s2) -> Prop (BStep (If b c1 c2) s s2)
    | BWhileF :: b:BExp -> c:Com -> s:{State | not (bval b s)} 
              -> Prop (BStep (While b c) s s)
    | BWhileT :: b:BExp -> c:Com -> s1:{State | bval b s1} -> s1':State -> s2:State
              -> Prop (BStep c s1 s1') -> Prop (BStep (While b c) s1' s2)
              -> Prop (BStep (While b c) s1 s2)
  @-}  
\end{code}

We can say that a program c1 is simulated by a program c2 when:

IF executing c1 takes starting state s to final state s', THEN executing c2
with the same starting state s also takes s to the same final state s'/

For proving c1 simulates c2, we can use the type alias
Sim = State -> State -> BStep -> BStep
which takes in a starting state s, final state s', a proof that c1 takes 
s to s', and returns a proof that c2 takes s to s'.

\begin{code}
{-@ lem_semi :: c1:_ -> c2:_ -> c3:_ -> s:_ -> s3:_
      -> Prop (BStep (Seq (Seq c1 c2) c3) s s3)
      -> Prop (BStep (Seq c1 (Seq c2 c3)) s s3) 
  @-}
lem_semi :: Com -> Com -> Com -> State -> State -> BStep -> BStep  
lem_semi c1 c2 c3 s s3 (BSeq c1c2 _c3 _s s2 _s3 c1c2_s_s2 c2_s2_s3)
  = case c1c2_s_s2 of
     BSeq _c1 _c2 __s s1 _s2 c1_s_s1 c2_s1_s2 ->
       BSeq c1 (Seq c2 c3) s s1 s3  c1_s_s1 c2c3_s1_s3 
       where
         c2c3_s1_s3 = BSeq c2 c3 s1 s2 s3 c2_s1_s2 c3_s2_s3


{- 

                           "c2_s1_s2"         "c3_s2_s3"
                           --------------     --------------
        "c1_s_s1"          BStep c2 s1 s2     BStep c3 s2 s3
        -------------      --------------------------------- [BSeq]
        BStep c1 s s1      BStep (c2;c3) s1 s3
        --------------------------------------- [BSeq]
        BStep (c1; (c2; c3)) s s3
       
-}        
\end{code}

We say that two programs are equivalent if c1 simulates c2 and c2 simulates c1.

Lets prove the equivalence of Seq c1 (Seq c2 c3) and Seq (Seq c1 c2) c3 by
proving Sim in the other direction

\begin{code}
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
\end{code}

Lets prove the equivalence of While False c and Skip by proving both directions

\begin{code}
{-@ lem_while_false_skip :: c:Com -> Sim (While ff c) Skip @-}
lem_while_false_skip :: Com -> SimT
lem_while_false_skip c = \s t (BWhileF {}) ->  BSkip s 


{-@ lem_while_false_skip' :: c:Com -> Sim Skip (While ff c) @-}
lem_while_false_skip' :: Com -> SimT
lem_while_false_skip' c = \s t (BSkip {}) -> BWhileF ff c s
\end{code}


What are some other equivalences within this language?

 - (x=2;y=2) == (y=2;x=2)

 - while(false) == skip

 - skip ; c == c

 - if true c1 c2 == c1

 - if false c1 c2 == c2

 - if b c c == c

\end{document}
