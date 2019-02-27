{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_27 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
import           Expressions hiding (And)
import           Imp 
import 	         BigStep

id x = x 

--------------------------------------------------------------------------------
-- | Small-step Semantics 
--------------------------------------------------------------------------------
{- 

  ------------------------------- [SAssign]
  (x:=a, s) -> (SKIP, asgn x a s)

  ------------------------------- [SSeq1]
  (Skip; c, s) -> (c, s)

  (c1, s) -> (c1', s')
  ------------------------------- [SSeq2]
  (c1; c2, s) -> (c1';c2, s')

  bval b s == True
  ------------------------------- [SIfT]
  (IF b c1 c2, s) -> (c1, s)

  bval b s == False 
  ------------------------------- [SIfT]
  (IF b c1 c2, s) -> (c2, s)

  bval b s == False 
  ------------------------------- [SWhileF]
  (WHILE b c, s) -> (SKIP, s)

  bval b s == True  
  ----------------------------------- [SWhileT]
  (WHILE b c, s) -> (c; WHILE b c, s)

 -}


data SStepProp where
  SStep :: Com -> State -> Com -> State -> SStepProp 

data SStepProof where 
    SAssign :: Vname -> AExp -> State -> SStepProof 
    SSeq1   :: Com   -> State -> SStepProof 
    SSeq2   :: Com   -> Com -> Com -> State -> State -> SStepProof -> SStepProof
    SIfT    :: BExp  -> Com -> Com -> State -> SStepProof 
    SIfF    :: BExp  -> Com -> Com -> State -> SStepProof 
    SWhileT :: BExp  -> Com -> State -> SStepProof
    SWhileF :: BExp  -> Com -> State -> SStepProof


{-@ data SStepProof where 
    SAssign :: x:_ -> a:_ -> s:_
            -> Prop (SStep (Assign x a) s Skip (asgn x a s)) 
  | SSeq1   :: c:_ -> s:_
            -> Prop (SStep (Seq Skip c) s c s) 
  | SSeq2   :: c1:_ -> c1':_ -> c2:_ -> s:_ -> s':_
            -> Prop (SStep c1 s c1' s')
            -> Prop (SStep (Seq c1 c2) s  (Seq c1' c2) s')
  | SIfT    :: b:_ -> c1:_ -> c2:_ -> s:{_ | bval b s} 
            -> Prop (SStep (If b c1 c2) s c1 s) 
  | SIfF    :: b:_ -> c1:_ -> c2:_ -> s:{_ | not (bval b s)} 
            -> Prop (SStep (If b c1 c2) s c2 s) 
  | SWhileF :: b:_ -> c:_ -> s:{_ | not (bval b s)}
            -> Prop (SStep (While b c) s Skip s) 
  | SWhileT :: b:_ -> c:_ -> s:{_ | (bval b s)}
            -> Prop (SStep (While b c) s (Seq c (While b c)) s)
@-}



-- IF (c, s) -> (c', s') THEN c /= SKIP
{-@ lem_not_skip :: c:_ -> c':_ -> s:_ -> s':_ -> 
       Prop (SStep c s c' s') -> { c /= Skip}
  @-}
lem_not_skip :: Com -> Com -> State -> State -> SStepProof -> Proof 
lem_not_skip c c' s s' foo = () 

lem_not_skip c c' s s' (SAssign {}) = () 

lem_not_skip c c' s s' (SSeq1 _c _s {}) {- :: Prop (Skip; _c) _s _c _s -}   = () 
 -- _c = c' 
 -- _s = s = s' 
 --  c = Skip; _c =/= Skip

lem_not_skip c c' s s' (SSeq2 {})   = () 
lem_not_skip c c' s s' (SIfT {})    = () 
lem_not_skip c c' s s' (SIfF {})    = () 
lem_not_skip c c' s s' (SWhileF {}) = () 
lem_not_skip c c' s s' (SWhileT {}) = () 







-- A helper function that "unfolds" a while loop once
{-@ reflect unWhile @-}
unWhile :: BExp -> Com -> Com 
unWhile b c = If b (Seq c (While b c)) Skip 