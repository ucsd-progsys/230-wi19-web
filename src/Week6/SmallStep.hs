{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module SmallStep where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions hiding (And)
import           Imp 
import           BigStep 

--------------------------------------------------------------------------------
-- | Small-step Semantics 
--------------------------------------------------------------------------------

data SStepP where
  SStep :: Com -> State -> Com -> State -> SStepP 

data SStep where 
    SAssign :: Vname -> AExp -> State -> SStep 
    SSeq1   :: Com   -> State -> SStep 
    SSeq2   :: Com   -> Com -> Com -> State -> State -> SStep -> SStep 
    SIfT    :: BExp  -> Com -> Com -> State -> SStep 
    SIfF    :: BExp  -> Com -> Com -> State -> SStep 
    SWhile  :: BExp  -> Com -> State -> SStep 

{-@ data SStep where 
    SAssign :: x:Vname -> a:AExp -> s:State 
            -> Prop (SStep (Assign x a) s Skip (asgn x a s)) 
  | SSeq1   :: c:Com -> s:State 
            -> Prop (SStep (Seq Skip c) s c s) 
  | SSeq2   :: c1:Com -> c1':Com  -> c2:Com -> s:State -> s':State 
            -> Prop (SStep c1 s c1' s')
            -> Prop (SStep (Seq c1 c2) s  (Seq c1' c2) s')
  | SIfT    :: b:BExp  -> c1:Com  -> c2:Com -> s:{State | bval b s} 
            -> Prop (SStep (If b c1 c2) s c1 s) 
  | SIfF    :: b:BExp  -> c1:Com  -> c2:Com -> s:{State | not (bval b s)} 
            -> Prop (SStep (If b c1 c2) s c2 s) 
  | SWhile  :: b:BExp  -> c:Com  -> s:State 
            -> Prop (SStep (While b c) s (unWhile b c) s) 
@-}

-- A helper function that "unfolds" a while loop once
{-@ reflect unWhile @-}
unWhile :: BExp -> Com -> Com 
unWhile b c = If b (Seq c (While b c)) Skip 

--------------------------------------------------------------------------------
-- | Multiple steps 
--------------------------------------------------------------------------------

data SStepsP where 
  SSteps :: Com -> State -> Com -> State -> SStepsP 

data SSteps where 
  SS0 :: Com -> State -> SSteps
  SS1 :: Com -> State -> Com -> State -> Com -> State -> SStep -> SSteps -> SSteps 

{-@  data SSteps where 
       SS0 :: c:Com -> s:State -> Prop (SSteps c s c s) 
     | SS1 :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c3:_ -> s3:_ 
           -> Prop (SStep  c1 s1 c2 s2)
           -> Prop (SSteps c2 s2 c3 s3) 
           -> Prop (SSteps c1 s1 c3 s3) 
@-}

-- TODO example 7

{-@ inc :: Int -> Int @-}
inc :: Int -> Int 
inc x = x + 1

{-@ lemma_sstep_skip :: c1:_ -> s1:_ -> c2:_ -> s2:_ 
                     -> Prop (SStep c1 s1 c2 s2) 
                     -> { c1 /= Skip }  
  @-}
lemma_sstep_skip :: Com -> State -> Com -> State -> SStep -> Proof 
lemma_sstep_skip = undefined

{-@ lemma_7_11 :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c2':_ -> s2':_ 
              -> Prop (SStep c1 s1 c2  s2 ) 
              -> Prop (SStep c1 s1 c2' s2') 
              -> { c2 == c2' && s2 == s2' }
  @-}
lemma_7_11 :: Com -> State -> Com -> State -> Com -> State -> SStep -> SStep -> Proof 
lemma_7_11 _ _ _ _ _ _ (SAssign x a s) (SAssign {}) 
  = ()
lemma_7_11 _ _ _ _ _ _ (SSeq1 c s)     (SSeq1 {}) 
  = ()
lemma_7_11 _ _ _ _ _ _ (SSeq1 {})      (SSeq2 c1 c1' c2 s s' c1_c1') 
  = lemma_sstep_skip c1 s c1' s' c1_c1' 
lemma_7_11 _ _ _ _ _ _ (SSeq2 c1 c1' c2 s s' c1_c1') (SSeq2 _ c1'' _ _ s'' c1_c1'') 
  = lemma_7_11 c1 s c1' s' c1'' s'' c1_c1' c1_c1''
lemma_7_11 _ _ _ _ _ _ (SSeq2 c1 c1' c2 s s' c1_c1') (SSeq1 {})
  = lemma_sstep_skip c1 s c1' s' c1_c1' 
lemma_7_11 _ _ _ _ _ _ (SIfT b c1 c2 s) (SIfT {}) 
  = ()
lemma_7_11 _ _ _ _ _ _ (SIfF b c1 c2 s) (SIfF {}) 
  = () 
lemma_7_11 _ _ _ _ _ _ (SWhile b c s) (SWhile {}) 
  = ()

--------------------------------------------------------------------------------
-- | Equivalence of big-step and small-step semantics
--   Big Step implies Small Step  
--------------------------------------------------------------------------------


{-@ lemma_7_12 :: c:_ -> s:_ -> t:_ -> Prop (BStep c s t) -> Prop (SSteps c s Skip t) @-}
lemma_7_12 :: Com -> State -> State -> BStep -> SSteps 
lemma_7_12 c s t (BSkip {}) 
  = SS0 c s 

lemma_7_12 c s t (BAssign x a _) 
  = ss1 c s Skip t (SAssign x a s) 

lemma_7_12 c s t (BIfT b c1 c2 _ _ s_c1_t) 
  = SS1 (If b c1 c2) s c1 s Skip t 
      (SIfT b c1 c2 s) 
      (lemma_7_12 c1 s t s_c1_t)

lemma_7_12 c s t (BIfF b c1 c2 _ _ s_c2_t) 
  = SS1 (If b c1 c2) s c2 s Skip t 
      (SIfF b c1 c2 s) 
      (lemma_7_12 c2 s t s_c2_t)

{- (W b cc, s) 
   --SWhile--> (unWhile b cc, s) 
   --SIfF----> (Skip, s)
 -} 
lemma_7_12 c s t (BWhileF b cc _) 
  = SS1 (While b cc) s (unWhile b cc) s Skip s 
      (SWhile b cc s) 
      (ss1 (unWhile b cc) s Skip s (SIfF b (Seq cc (While b cc)) Skip s))

-- TODO: IMPLICITS!!!!
{- (W b cc, s) 
    --SWhile-->  (unWhile b cc     , s)     (c1, tx1)
    --SIfT---->  (Seq cc   (W b cc), s)     (c2, tx2)
    ---------->* (Seq Skip (W b cc), s1)    (c3, tx3)
    --SSeq1--->  (W b cc           , s1)    (c4, tx4)
    ---------->* (Skip             , t)     (c5, tx5)

-}
lemma_7_12 c s t (BWhileT b cc _ s1 _ s_cc_s1 s1_wbc_t) 
  -- ideally: tx1 `SS1` tx2 `SS1` tx3 `ssn` tx4 `SS1` tx5
  = SS1 c s c1 s Skip t tx1 
     (SS1 c1 s c2 s Skip t tx2 
       (ssn c2 s c3 s1 Skip t tx3 
         (SS1 c3 s1 c4 s1 Skip t tx4 
           tx5 
         )
       ) 
     ) 
  where 
    tx1    = SWhile b cc s 
    tx2    = SIfT  b c2 Skip s  
    tx3    = lemma_7_13 cc s Skip s1 c4 tx3a
    tx3a   = lemma_7_12 cc s s1 s_cc_s1 
    tx4    = SSeq1      c4 s1
    tx5    = lemma_7_12 c4 s1 t s1_wbc_t

    c1     = unWhile b cc 
    c2     = Seq cc   (While b cc)
    c3     = Seq Skip (While b cc)
    c4     = While b cc 

{- (Seq c1 c2, s) 
   --------->* (Seq Skip c2, s1)      (cmd1, 1)
   --SSeq1-->  (c2         , s1)      (    , 2)
   --------->* (Skip       , t )      (    , 3)
 -}
lemma_7_12 c s t (BSeq c1 c2 _ s1 _ s_c1_s1 s1_c2_t) 
  = ssn c s cmd1 s1 Skip t tx1 
      ( SS1 cmd1 s1 c2 s1 Skip t tx2 
         tx3 
      )
  where 
    tx3  = lemma_7_12 c2 s1 t s1_c2_t
    tx2  = SSeq1 c2 s1
    tx1  = lemma_7_13 c1 s Skip s1 c2 tx1a
    tx1a = lemma_7_12 c1 s s1 s_c1_s1 
    cmd1 = Seq Skip c2


{-@ lemma_7_13 :: c1:_ -> s1:_ -> c1':_ -> s1':_ -> c2:_ 
              -> Prop (SSteps c1 s1 c1' s1') 
              -> Prop (SSteps (Seq c1 c2) s1 (Seq c1' c2) s1') 
  @-}
lemma_7_13 :: Com -> State -> Com -> State -> Com -> SSteps -> SSteps 
lemma_7_13 c1 s1 _   _   c2 (SS0 {}) 
  = SS0 (Seq c1 c2) s1 
lemma_7_13 c1 s1 c1' s1' c2 (SS1 _ _ c1'' s1'' _ _ c1_c1'' c1''_c1') 
  = SS1 (Seq c1 c2) s1 cmd1 s1'' cmd2 s1' tx1 tx2 
  where 
    tx1  = SSeq2 c1 c1'' c2 s1 s1'' c1_c1''
    tx2  = lemma_7_13 c1'' s1'' c1' s1' c2 c1''_c1' 
    cmd1 = Seq c1'' c2 
    cmd2 = Seq c1'  c2

{- Informal proof of lemma_7_13 

                (Seq c1   c2, s1  )

   --SSeq2--->  (Seq c1'' c2, s1'')    (cmd1, tx1) 
      IH
   ---------->* (Seq c1' c2, s1' )     (cmd2, tx2)

 -}  

{-@ ss1 :: c1:_ -> s1:_ -> c2:_ -> s2:_ 
        -> Prop (SStep c1 s1 c2 s2) 
        -> Prop (SSteps c1 s1 c2 s2) 
  @-}
ss1 :: Com -> State -> Com -> State -> SStep -> SSteps 
ss1 c1 s1 c2 s2 pf = SS1 c1 s1 c2 s2 c2 s2 pf (SS0 c2 s2) 

{-@ ssn :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c3:_ -> s3:_ 
        -> Prop (SSteps c1 s1 c2 s2) 
        -> Prop (SSteps c2 s2 c3 s3) 
        -> Prop (SSteps c1 s1 c3 s3) 
  @-}
ssn :: Com -> State -> Com -> State -> Com -> State -> SSteps -> SSteps -> SSteps 
ssn c1 s1 c2 s2 c3 s3 (SS0 {}) rest 
  = rest 
ssn c1 s1 c2 s2 c3 s3 (SS1 _ _ c1' s1' _ _ c1_c1' c1'_c2) rest 
  = SS1 c1 s1 c1' s1' c3 s3 c1_c1' (ssn c1' s1' c2 s2 c3 s3 c1'_c2 rest) 


--------------------------------------------------------------------------------
-- | Equivalence of big-step and small-step semantics
--   Small Step implies Big Step  
--------------------------------------------------------------------------------
{-@ lemma_7_14 :: c:_ -> s:_ -> t:_ -> Prop (SSteps c s Skip t) -> Prop (BStep c s t)  @-}
lemma_7_14 :: Com -> State -> State -> SSteps -> BStep 
lemma_7_14 _ s _ (SS0 {}) 
  = BSkip s
lemma_7_14 c s t (SS1 _ _ c' s' _ _ c_c' c'_skip) 
  = lemma_7_15 c s c' s' t c_c' (lemma_7_14 c' s' t c'_skip) 


{-@ lemma_7_15 :: c:_ -> s:_ -> c':_ -> s':_ -> t:_ 
               -> Prop (SStep c s c' s') 
               -> Prop (BStep c' s' t)
               -> Prop (BStep c s t) 
  @-}

lemma_7_15 :: Com -> State -> Com -> State -> State -> SStep -> BStep -> BStep
-- c  = Assign x a
-- c' = Skip 
lemma_7_15 c s c' s' t (SAssign x a _) (BSkip {}) 
  = BAssign x a s 

-- c  = Seq Skip c'
lemma_7_15 c s _ _ t (SSeq1 c' _) s_c'_t 
  = BSeq Skip c' s s t (BSkip s) s_c'_t 

-- c  = Seq c1  c2 
-- c' = Seq c1' c2
lemma_7_15 c s c' s' t (SSeq2 c1 c1' c2 _ _ c1_c1') (BSeq _ _ _ s'' _ c1'_s'_s'' c2_s''_t) 
  = BSeq c1 c2 s s'' t c1_s_s'' c2_s''_t 
  where 
    c1_s_s'' = lemma_7_15 c1 s c1' s' s'' c1_c1' c1'_s'_s''

-- c  = If b c1 c2     
-- c' = c1 
-- s' = s 
lemma_7_15 c s c' _ t (SIfT b c1 c2 _) c1_s_t 
  = BIfT b c1 c2 s t c1_s_t 

-- c  = If b c1 c2     
-- c' = c2 
-- s' = s 
lemma_7_15 c s c' s' t (SIfF b c1 c2 _) c2_s_t 
  = BIfF b c1 c2 s t c2_s_t 

-- c  = While   b cc 
-- c' = unWhile b cc
-- s' = s
lemma_7_15 c s c' _ t (SWhile b cc _) (BIfT _ ccw _ _ _ (BSeq _ w _ s1 _ cc_s_s1 w_s1_t))
  = BWhileT b cc s s1 t cc_s_s1 w_s1_t 

-- c     = While   b cc
-- c'    = If b ccw Skip unWhile b cc
-- s', t = s
lemma_7_15 c s c' s' t (SWhile b cc _) (BIfF _ ccw _ _ _ (BSkip {}))
  = BWhileF b cc s 
