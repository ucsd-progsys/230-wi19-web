{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module BigStep where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions hiding (And)
import           Imp 

{- 
  BStep c s1 s2 

  ------------------[BSkip]
    BStep Skip s s


    s' = set x (aval a s) s
  ----------------------------------[BAssign]
    BStep (x := a) s s'


    BStep c1 s smid    BStep c2 smid s'
  ----------------------------------------[BSeq]
    BStep (c1; c2) s s' 


    bval b s1 = TRUE      BStep c1 s s'
  ----------------------------------------
    BStep (If b c1 c2) s s' 

    bval b s = FALSE     BStep c2 s s'
  -------------------------------
    BStep (If b c1 c2) s s' 

    WHILE 
 -}

--------------------------------------------------------------------------------
-- | Big-step Semantics 
--------------------------------------------------------------------------------

data BStepP where
  BStep :: Com -> State -> State -> BStepP 

data BStep where 
  BSkip   :: State -> BStep 
  BAssign :: Vname -> AExp -> State -> BStep 
  BSeq    :: Com   -> Com  -> State  -> State -> State -> BStep -> BStep -> BStep 
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

--------------------------------------------------------------------------------

{-@ reflect cmd_1 @-}
cmd_1 = "x" <~ N 5

{-@ reflect cmd_2 @-}
cmd_2 = "y" <~ (V "x")

{-@ reflect cmd_1_2 @-}
cmd_1_2 = cmd_1 @@ cmd_2 

{-@ reflect prop_set @-}
prop_set cmd x v s = BStep cmd s (S.set s x v)

{-@ step_1 :: s:State -> Prop (prop_set cmd_1 {"x"} 5 s)  @-}
step_1 s =  BAssign "x" (N 5) s

{-@ step_2 :: s:{State | S.get s "x" == 5} -> Prop (prop_set cmd_2 {"y"} 5 s) @-}
step_2 s = BAssign "y" (V "x") s

{-@ step_1_2 :: s:State -> Prop (BStep cmd_1_2 s (S.set (S.set s {"x"} 5) {"y"} 5)) @-}
step_1_2 s = BSeq cmd_1 cmd_2 s s1 s2 (step_1 s) (step_2 s1) 
  where 
    s1     = S.set s  "x" 5 
    s2     = S.set s1 "y" 5

-------------------------------------------------------------------------------
-- step practice
-------------------------------------------------------------------------------
{-@ lemma_7_1_a :: c1:_ -> c2:_ -> c3:_ -> s:_ -> s3:_
      -> Prop (BStep (Seq (Seq c1 c2) c3) s s3)
      -> Prop (BStep (Seq c1 (Seq c2 c3)) s s3) 
  @-}
lemma_7_1_a :: Com -> Com -> Com -> State -> State -> BStep -> BStep 
lemma_7_1_a _ _ _ s s3 (BSeq c12 c3 _ s2 _ (BSeq c1 c2 _ s1 _  bs1 bs2) bs3) 
  = BSeq c1 (Seq c2 c3) s s1 s3 bs1 (BSeq c2 c3 s1 s2 s3 bs2 bs3)

{-@ lemma_7_1_b :: c1:_ -> c2:_ -> c3:_ -> s:_ -> s3:_
      -> Prop (BStep (Seq c1 (Seq c2 c3)) s s3) 
      -> Prop (BStep (Seq (Seq c1 c2) c3) s s3)
  @-}
lemma_7_1_b :: Com -> Com -> Com -> State -> State -> BStep -> BStep 
lemma_7_1_b _ _ _ s s3 (BSeq c1 (Seq c2 c3) _ s1 _ bs1 (BSeq _ _ _ s2 _ bs2 bs3))
  = BSeq (Seq c1 c2) c3 s s2 s3 (BSeq c1 c2 s s1 s2 bs1 bs2) bs3

-------------------------------------------------------------------------------
-- | We say (c1 `Sim` c2) or `c1` is simulated by `c2` if 
--   the transitions of `c1` are contained within those of `c2`
-------------------------------------------------------------------------------

{-@ type Sim C1 C2 = s:State -> t:State -> Prop (BStep C1 s t) -> Prop (BStep C2 s t) @-}
type SimT = State -> State -> BStep -> BStep 

data And a b = And a b

-- | We say `(c1 ~ c2)` if `c1 Sim c2` and `c2 Sim c1` 
{-@ type Equiv C1 C2 = And (Sim C1 C2) (Sim C2 C1) @-}
type EquivT = And SimT SimT 

-------------------------------------------------------------------------------

{-@ lemma_7_3_a :: b:BExp -> c:Com -> Sim (While b c) (If b (Seq c (While b c)) Skip) @-}
lemma_7_3_a :: BExp -> Com -> SimT
lemma_7_3_a b c _ _ (BWhileF _ _ s) 
  = BIfF b (Seq c (While b c)) Skip s s (BSkip s)

lemma_7_3_a b c s t (BWhileT _ _ _ s1 _ s_s1 s1_t) 
  = BIfT b (Seq c (While b c)) Skip s t (BSeq c (While b c) s s1 t s_s1 s1_t)

{-@ lemma_7_3_b :: b:_ -> c:_ -> Sim (If b (Seq c (While b c)) Skip) (While b c) @-}
lemma_7_3_b :: BExp -> Com -> SimT
lemma_7_3_b b c s t (BIfF _ _ Skip _ _ (BSkip _))
  = BWhileF b c s
lemma_7_3_b b c _ _ (BIfT _ _ _ s t (BSeq _ _ _ s1 _ s_s1 s1_t))
  = BWhileT b c s s1 t s_s1 s1_t

{-@ lemma_7_3 :: b:BExp -> c:Com -> Equiv (While b c) (If b (Seq c (While b c)) Skip) @-}
lemma_7_3  :: BExp -> Com -> EquivT
lemma_7_3 b c = And (lemma_7_3_a b c) (lemma_7_3_b b c)

-------------------------------------------------------------------------------

{-@ lemma_7_4_a :: b:_ -> c:_ -> Sim (If b c c) c @-}
lemma_7_4_a :: BExp -> Com -> SimT 
lemma_7_4_a b c s t (BIfT _ _ _ _ _ st) = st 
lemma_7_4_a b c s t (BIfF _ _ _ _ _ st) = st 

{-@ lemma_7_4_b :: b:_ -> c:_ -> Sim c (If b c c) @-}
lemma_7_4_b :: BExp -> Com -> SimT 
lemma_7_4_b b c s t st 
  | bval b s  = BIfT b c c s t st 
  | otherwise = BIfF b c c s t st 

{-@ lemma_7_4 :: b:BExp -> c:Com -> Equiv (If b c c) c @-}
lemma_7_4 :: BExp -> Com -> EquivT 
lemma_7_4 b c = And (lemma_7_4_a b c) (lemma_7_4_b b c)

---------------------------------------------------------------------------------

{-@ sim_refl :: c:Com -> Sim c c @-}
sim_refl :: Com -> SimT 
sim_refl c = \_ _ -> id 

{-@ sim_trans :: c1:_ -> c2:_ -> c3:_ -> Sim c1 c2 -> Sim c2 c3 -> Sim c1 c3 @-}
sim_trans :: Com -> Com -> Com -> SimT -> SimT -> SimT 
sim_trans c1 c2 c3 r12 r23 = \s t -> r23 s t . r12 s t

---------------------------------------------------------------------------------

{-@ equiv_symm :: c1:_ -> c2:_ -> (Equiv c1 c2) -> (Equiv c2 c1) @-} 
equiv_symm :: Com -> Com -> EquivT -> EquivT 
equiv_symm c1 c2 (And p12 p21) = And p21 p12 

{-@ equiv_refl :: c:Com -> Equiv c c @-}
equiv_refl :: Com -> EquivT
equiv_refl c = And (sim_refl c) (sim_refl c) 

{-@ equiv_trans :: c1:_ -> c2:_ -> c3:_ -> Equiv c1 c2 -> Equiv c2 c3 -> Equiv c1 c3 @-}
equiv_trans :: Com -> Com -> Com -> EquivT -> EquivT -> EquivT 
equiv_trans c1 c2 c3 (And r12 r21) (And r23 r32) 
        = And r13 r31 
  where 
    r13 = sim_trans c1 c2 c3 r12 r23 
    r31 = sim_trans c3 c2 c1 r32 r21

---------------------------------------------------------------------------------

{-@ lemma_5 :: b:_ -> c:_ -> c':_ -> Sim c c' -> Sim (While b c) (While b c') @-}
lemma_5 :: BExp -> Com -> Com -> SimT -> SimT 
lemma_5 b c c' r s t (BWhileF _ _ _)                = BWhileF b c' s 
lemma_5 b c c' r s t (BWhileT _ _ _ s1 _ s_s1 s1_t) = BWhileT b c' s s1 t s_s1' s1_t' 
  where 
    s_s1'                                           = r s s1 s_s1 
    s1_t'                                           = lemma_5 b c c' r s1 t s1_t


-- Exercise? 

{-@ lemma_7_6 :: b:_ -> c1:_ -> c2:_ -> s:_ -> t:_
              -> Sim c1 c2 
              -> Prop (BStep (While b c1) s t)
              -> Prop (BStep (While b c2) s t)
  @-}
lemma_7_6 :: BExp -> Com -> Com -> State -> State -> SimT -> BStep -> BStep 
lemma_7_6 b c c' s t r (BWhileF _ _ _)                = BWhileF b c' s 
lemma_7_6 b c c' s t r (BWhileT _ _ _ s1 _ s_s1 s1_t) = BWhileT b c' s s1 t s_s1' s1_t'
  where 
    s_s1'                                             = r s s1 s_s1 
    s1_t'                                             = lemma_7_6 b c c' s1 t r s1_t

---------------------------------------------------------------------------------
-- | IMP is Deterministic 
---------------------------------------------------------------------------------
{-@ lemma_7_9 :: s:_ -> t:_ -> t':_ -> c:_ 
              -> Prop (BStep c s t) -> Prop (BStep c s t') -> { t == t' }
  @-}
lemma_7_9 :: State -> State -> State -> Com -> BStep -> BStep -> Proof

lemma_7_9 s t t' Skip         (BSkip {})   (BSkip {}) 
  = ()

lemma_7_9 s t t' (Assign x a) (BAssign {}) (BAssign {})
  = () 

lemma_7_9 s t t' (Seq c1 c2)  (BSeq _ _ _ s1 s2 s_s1 s1_s2) (BSeq _ _ _ s1' s2' s_s1' s1_s2') 
  = lemma_7_9 s1_eq_s1' s2 s2' c2 s1_s2 s1_s2'        where s1_eq_s1' = s1 ? lemma_7_9 s  s1 s1' c1 s_s1  s_s1'

lemma_7_9 s t t' (If b c1 c2) (BIfT _ _ _ _ _t c1_s_t) (BIfT _ _ _ _ _t' c1_s_t')
  = lemma_7_9 s t t' c1 c1_s_t c1_s_t' 

lemma_7_9 s t t' (If b c1 c2) (BIfF _ _ _ _ _t c2_s_t) (BIfF _ _ _ _ _t' c2_s_t')
  = lemma_7_9 s t t' c2 c2_s_t c2_s_t' 

lemma_7_9 s t t' (While b c)  (BWhileF {}) (BWhileF {}) 
  = () 

lemma_7_9 s t t' (While b c)  (BWhileT _ _ _ s1 _ s_s1 s1_t) (BWhileT _ _ _ s1' _ s_s1' s1_t') 
  = lemma_7_9 s1_eq_s1' t t' (While b c) s1_t s1_t'   where s1_eq_s1' = s1 ? lemma_7_9 s s1 s1' c s_s1 s_s1'


