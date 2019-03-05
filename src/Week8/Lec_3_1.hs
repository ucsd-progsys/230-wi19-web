{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_3_1 where

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
lem_not_skip c c' s s' (SAssign {}) = () 

lem_not_skip c c' s s' (SSeq1 _c _s) {- :: Prop (Skip; _c) _s _c _s -}   = () 
 -- _c = c' 
 -- _s = s = s' 
 --  c = Skip; _c =/= Skip

lem_not_skip c c' s s' (SSeq2 {})   = () 
lem_not_skip c c' s s' (SIfT {})    = () 
lem_not_skip c c' s s' (SIfF {})    = () 
lem_not_skip c c' s s' (SWhileF {}) = () 
lem_not_skip c c' s s' (SWhileT {}) = () 


----------------------------------------------------------------------------------

{-@ lem_ss_det :: c:_ -> s:_ -> c1:_ -> s1:_ -> c2:_ -> s2:_ 
   -> Prop (SStep c s c1 s1) 
   -> Prop (SStep c s c2 s2) 
   -> { c1 = c2  && s1 = s2 } 
  @-}

lem_ss_det :: Com -> State -> Com -> State -> Com -> State 
   -> SStepProof 
   -> SStepProof 
   -> Proof 

lem_ss_det c s c1 s1 c2 s2 
  (SAssign {}) -- c == Assign x a 
  (SAssign {}) -- c1 = c2 = Skip, s1 = s2 = asgn x a s     
  = () 

lem_ss_det c s c1 s1 c2 s2 
  (SSeq1 {}) -- c == SKIP; c' 
  (SSeq1 {}) -- c1 = c2 = c', s1 = s2 = s
  = () 

lem_ss_det c s c1 s1 c2 s2 
  (SSeq1 {})                             -- c == SKIP; FOO 
  (SSeq2 cA cA' _FOO _s _s2 cA_s_cA'_s2) -- c == cA  ; FOO 
  = impossible ("really" ? lem_not_skip cA cA' s _s2 cA_s_cA'_s2)

lem_ss_det c s c1 s1 c2 s2 
  (SSeq2 cA cA' _FOO _s _s2 cA_s_cA'_s2) -- c == SKIP ; FOO
  (SSeq1 {}) -- c == SKIP; FOO 
  = lem_not_skip cA cA' s _s2 cA_s_cA'_s2 


lem_ss_det c s c1 s1 c2 s2 
  (SSeq2 cA cA'  cB _ _s1 cA_s_cA'_s1)  
  (SSeq2 _  cA'' _  _ _s2 cA_s_cA''_s2)
  -- c == cA  ; cB 
  -- c1 == cA' ; CB     
  -- c2 == cA''; CB     
  -- cA_s_cA'_s1  
  -- cA_s_cA''_s2 
  = lem_ss_det cA s cA' s1 cA'' s2 cA_s_cA'_s1  cA_s_cA''_s2  --  cA' = cA'' && s1 = s2                                  

lem_ss_det c s c1 s1 c2 s2 
  (SIfF {}) 
  (SIfF {}) 
  = ()

lem_ss_det c s c1 s1 c2 s2 
  (SIfT {}) 
  (SIfT {}) 
  = ()

lem_ss_det c s c1 s1 c2 s2 
  (SWhileT {}) 
  (SWhileT {}) 
  = ()

lem_ss_det c s c1 s1 c2 s2 
  (SWhileF {}) 
  (SWhileF {}) 
  = ()


{-@ lem_michael :: c:_ -> s:_ -> s':_
      -> Prop (SStep c s Skip s')
      -> Prop (BStep c s s')
  @-}
lem_michael :: Com -> State -> State -> SStepProof -> BStep
lem_michael c s s' (SAssign x a _ ) 
  -- c  == Assign x a 
  -- s' == asgn x a s
  = BAssign x a s -- Prop (BStep (Assign x a) s s')

lem_michael c s s' c_s_skip_s' = undefined












-- A helper function that "unfolds" a while loop once
{-@ reflect unWhile @-}
unWhile :: BExp -> Com -> Com 
unWhile b c = If b (Seq c (While b c)) Skip 
