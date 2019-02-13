{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Imp where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions hiding (And)

--------------------------------------------------------------------------------
-- | IMP Commands
--------------------------------------------------------------------------------

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

data Com 
  = Skip                      -- skip 
  | Assign Vname AExp         -- x := a
  | Seq    Com   Com          -- c1; c2
  | If     BExp  Com   Com    -- if b then c1 else c2
  | While  BExp  Com          -- while b c 
  deriving (Show)


{-@ reflect <~ @-}
x <~ a = Assign x a 

{-@ reflect @@ @-}
s1 @@ s2 = Seq s1 s2

-- x = y + 1; y = 2

ex_7_1 :: Com 
ex_7_1 = ("x" <~ Plus (V "y") (N 1))  @@ 
         ("y" <~ N 2)                 @@ 
         Skip 

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

{-@ data BStep [stepSize] where 
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

{-@ measure stepSize @-}
{-@ stepSize :: BStep -> Nat @-}
stepSize :: BStep -> Int 
stepSize (BSkip {})                = 0 
stepSize (BAssign {})              = 0 
stepSize (BSeq _ _ _ _ _ s1 s2)    = 1 + stepSize s1 + stepSize s2 
stepSize (BIfT _ _ _ _ _ s)        = 1 + stepSize s
stepSize (BIfF _ _ _ _ _ s)        = 1 + stepSize s
stepSize (BWhileF {})              = 0 
stepSize (BWhileT _ _ _ _ _ s1 s2) = 1 + stepSize s1 + stepSize s2  

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

{-@ measure sstepSize @-}
{-@ sstepSize :: SStep -> Nat @-} 
sstepSize :: SStep -> Int 
sstepSize (SSeq2 _ _ _ _ _ ss) = 1 + sstepSize ss 
sstepSize _                    = 0 

{-@ data SStep [sstepSize] where 
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

{-@  data SSteps [sstepsSize] where 
       SS0 :: c:Com -> s:State -> Prop (SSteps c s c s) 
     | SS1 :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c3:_ -> s3:_ 
           -> Prop (SStep  c1 s1 c2 s2)
           -> Prop (SSteps c2 s2 c3 s3) 
           -> Prop (SSteps c1 s1 c3 s3) 
@-}

{-@ measure sstepsSize          @-}  
{-@ sstepsSize :: SSteps -> Nat @-} 
sstepsSize :: SSteps -> Int 
sstepsSize (SS0 {})              = 0
sstepsSize (SS1 _ _ _ _ _ _ _ s) = 1 + sstepsSize s

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
