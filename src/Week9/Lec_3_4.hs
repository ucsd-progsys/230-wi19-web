{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_3_4 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
import           Expressions hiding (And)
import           Imp 
import 	         BigStep


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
  = BAssign x a s 

lem_michael c s s' (SSeq1 {}) 
  -- c  = SKIP; c1 
  -- c' = SKIP 
  -- c1 = SKIP
  = undefined -- :: Prop (BSTep (Seq SKIP SKIP) s s)

lem_michael c s s' (SSeq2 {}) -- :: SStep (c1;c2) s (c1';c2) s' 
  -- c  = c1; c2 
  -- c' = SKIP 
  = impossible "seq-is-not-skip"
  
lem_michael c s s' c_s_skip_s' = undefined


-------

data SStepsProp where
  SSteps :: Com -> State -> Com -> State -> SStepsProp 

data SStepsProof where
  Refl :: Com -> State -> SStepsProof
  Edge :: Com -> State -> Com -> State -> Com -> State -> SStepProof -> SStepsProof -> SStepsProof

{-@  data SStepsProof where
        Refl :: c:_ -> s:_ -> Prop (SSteps c s c s) 
      | Edge :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c3:_ -> s3:_
             -> Prop (SStep c1 s1 c2 s2)
             -> Prop (SSteps c2 s2 c3 s3)
             -> Prop (SSteps c1 s1 c3 s3)
  @-}

{-@ lem_sstep_bstep :: c:_ -> s:_ -> s':_ -> Prop (SSteps c s Skip s') -> Prop (BStep c s s') @-}
lem_sstep_bstep :: Com -> State -> State -> SStepsProof -> BStep 
lem_sstep_bstep c s s' (Refl {}) 
  = BSkip s 

lem_sstep_bstep (Assign {}) s s' (Edge _ _ c2 _s2 _ _ (SAssign x a _) (Refl {})) 
  -- c  = Assign x a
  -- c2 = Skip 
  -- s2 = asgn x a s
  = BAssign x a s -- Prop (BStep (Assign x a) s s')

lem_sstep_bstep (If b cThen cElse) s s' (Edge _ _ _cThen _ _ _ (SIfT {}) c2s2_c3s3) 
  -- lem_sstep_bstep cThen s s' c2s2_c3s3 :: Prop (BStep cThen s s')
  -- = undefined -- Prop (BStep (If b cThen cElse) s s')
  = BIfT b cThen cElse s s' (lem_sstep_bstep cThen s s' c2s2_c3s3)

lem_sstep_bstep (If b cThen cElse) s s' (Edge _ _ _cThen _ _ _ (SIfF {}) c2s2_c3s3) 
  = BIfF b cThen cElse s s' (lem_sstep_bstep cElse s s' c2s2_c3s3)

-- 1. COMMAND Is GETTING SMALLER 
-- 2. PATH is GETTING SMALLER 


{- 

   bval b s = True    BStep (cThen s s')
  ---------------------------------------- BIfT
   BStep (If b cThen cElse) s s' 
 -}
lem_sstep_bstep c s s' (Edge _c _s _c2 _s2 _ _ c1s1_c2s2  c2s2_c3s3) 
  = undefined 





{-@ lem_bstep_sstep :: c:_ -> s:_ -> s':_ -> Prop (BStep c s s') -> Prop (SSteps c s Skip s') @-}
lem_bstep_sstep :: Com -> State -> State -> BStep -> SStepsProof 
lem_bstep_sstep = undefined 







-- A helper function that "unfolds" a while loop once
{-@ reflect unWhile @-}
unWhile :: BExp -> Com -> Com 
unWhile b c = If b (Seq c (While b c)) Skip 
