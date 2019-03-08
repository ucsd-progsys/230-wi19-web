
Lem_sstep_bstep :: Com -> State -> State -> SStepsProof -> BStep
Lem_sstep_bstep c s s’ (Refl {}) = BSkip s
Lem_sstep_bstep (Assign {}) s s’ (Edge _ _ c2 _s2 _ _ (SAssign x a _) (Refl {})) ← Refl goes here because we are allowed to assume the program path is size 1,

= BAssign x a s

           Bval b s = True    BStep (cThen s s’)
       ---------------------------------------- BIfT
          BStep (If b cThen cElse) s s’


Lem_sstep_bstep (If b cThen cElse) s s’ (Edge _ _ _cThen _s2 _ _ (SIfT {}) c2s2_c3s3)
    -- c2s2_c3s3 :: lem_sstep_bstep cThen s s’ c2s2_c3s3 is a proof that (BStep cThen s s’)
= BifT b cThen cElse s s’ (lem_sstep_bstep cThen s s’ c2s2_c3s3)

What are we actually doing induction on? The path. Notice that the whileT makes the program get “bigger”, so we cannot do induction on the program size. This makes sense, program termination is built in to these SStepsProof objects, as they are finite data structures.

Lem_bstep_sstep :; Com -> State -> State -> BStep -> SStepsProof





Recall we have been connecting small-step and big-step semantics:
(c,s) -> … -> (Skip, s’) implies BigStep(c,s,s’)

Last lecture, we outlined some proofs talking about one small step at a time.

{-@ lem_michael :: c:_ -> s:_ -> s':_ -> Prop (SStep c s Skip s') -> Prop (BStep c s s') @-}

lem_michael :: c:Com -> s:State -> s’State -> pf:SStepProof -> BStep
“If (c,s) → (skip, s’) then BigStep c s s’ ”

-- Case holds easily
lem_michael c s s' (SSeq1 {})
-- c = SKIP; c1
-- c' = SKIP <--- final state
-- c1 = SKIP
  = -- :: must produce prop that Bigstep seq of skip skip starting in s goes to s
  -- have to apply BSeq rule multiple times

lem_michael c s s' (SSeq2 {})  -- :: SStep (c1; c2) s (c1'; c2) s'
-- c = c1; c2
-- c' = SKIP <--- final state
-- Should be impossible because we require it to step to skip and sseq2 doesn't step us to SKIP
  = impossible "seq-is-not-skip"


{-
In SWhileF we can transition to a skip
in SWhileT we don't sstep to a skip
have to handle the two if rules if left or right branch is a skip
-}

{-
how do we talk about sstepping zero or many times and that's equal to big step

if (c, s) ~>(0 or more) (SKIP, s'), then BSTEP c s s'
How do we write down "0 or more"
This looks like paths from earlier homework.
earlier "node" corresponds to (c, s)
earlier "edge" corresponds to (c, s) ~> (c', s')

Let's look how we defined this:
-}

-- Proposition for the reflexive, transitive closure of sstep
data SStepsProp where
  SSteps :: Com -> State -> Com -> State -> SStepsProp
            -- starting command and state to later command and state

data SStepsProof where
  Refl :: Com -> State -> SStepsProof
  Edge :: Com -> State -> Com -> State -> Com -> State -> SStepProof -> SStepsProof -> SStepsProof

{-@ data SStepsProof where
  Refl :: c:_ -> s:_ -> Prop (SSteps c s c s)
| Edge :: c1:_ -> s1:_ -> c2:_ -> s2:_ -> c3:_ -> s3:_ ->
          -> Prop (SStep c1 s1 c2 s2) -- edge-from c1-s1 to c2-s2
          -> Prop (SSteps c2 s2 c3 s3) -- path-from c2-s2 to c3-s3
          -> Prop (SSteps c1 s1 c3 s3) -- path-from c1-s1 to c3-s3
@-}
  -- ^ if I go from (c, s) ~> (c', s') ~>* (c'', s'')
  -- then (c, s) ~>* (c'', s'')

                --------------
                (c,s) -> (c,s)

Type: Com->State->SStepsProof

               (c,s) -> (c’,s’)     (c’,s’) ->* (c’’, s’’)
              --------------------------------------------
                        (c,s) ->* (c’’,s’’) 

type: Com->State->Com->State->Com->State->SStepProof->SStepProof
->SStepsProof


{-
Theorem that small step is equivalent to big step:
If (c, s) -->* (SKIP, s'),
then BStep c s s'
-}
{-@ lem_sstep_bstep :: c:_ -> s:_ -> s':_ -> Prop (SSteps c s Skip s') -> Prop (BStep c s s') @-}
lem_sstep_bstep :: Com -> State -> State -> SStepsProof -> BStep

-- ^ what do we do the induction on?
-- base state is c is SKIP which corresponds to Refl

lem_sstep_bstep c s s' (Refl {}) = BSkip s
lem_sstep_bstep c s s' (Edge _c s _c2 _s2 _skip _ c1s1_c2s2 {- (c1, s1) -> (c2, s2) -} c2s2_c3s3 {- (c2, s2) ->* (c3, s3) -}) =
                       -- presumably use induction on c2s2_c3s3
                       -- but we're stuck: who do we case split on?
                       -- Student Idea: split on SStep of c1s1_c2s2
                       -- let's try:
  case c1s1_c2s2 of
    (SAssign x a _) ->
      -- c = Assign x a
      -- what must c2 be? c2 = Skip
      -- what must s2 be? s2 = asgn x a s
      -- need to construct: Prop (BStep (Assign x a) s s')
      BAssign x a s -- this failed. Why? Doesn't know that s' = s3
                    -- need to case split on c2s2_c3s3 to show LH that it's Refl

  -- TODO: make this above case into a single top level match

lem_sstep_bstep (If b cThen cElse) s s' (Edge _ _ _cThen _ _ _ (SIfT {}) c2s2_c3s3) =
  -- lem_sstep_bstep cThen s s' c2s2_c3s3 :: Prop (BStep cThen s s')
  -- want Prop (BStep (If b cThen cElse) s s')
  = BIfT b cThen cElse s s' (lem_sstep_bstep cThen s s' c2s2_c3s3)
  {-
  bval b s = True   BStep cThen s s' <--- from the recursive call
  ----------------------------------- BIfT
  BStep (If b cThen cElse) s s'
  -}

-- IfF basically the same
lem_sstep_bstep (If b cThen cElse) s s' (Edge _ _ _cThen _ _ _ (SIfF {}) c2s2_c3s3) =
  = BIfF b cThen cElse s s' (lem_sstep_bstep cElse s s' c2s2_c3s3)

{-
So what are we actually doing induction on?
Trying to prove:
If (c, s) -->* (SKIP, s'),
then BStep c s s'
Which object are we doing induction on?
Student thought: doing induction on c because each step c gets smaller
How to answer question: Which thing are we doing recursive call on? Which thing is getting smaller?
Quiz:
1. Command is getting smaller
2. Something else is getting smaller

Looks like command is smaller. But in WhileT case the command doesn't get smaller
In this case While b c -> c; While b c which is not structurally smaller?

So what is getting smaller?
The path is getting smaller. SSteps can only encode finite sequences of reductions. This is encoded in the statement because we -->* (Skip, s')
So we are doing induction on the length of -->*
-}

-- Similarly, the other direction
{-@ lem_bstep_sstep :: c:_ -> s:_ -> s':_ -> Prop (BStep c s s') -> Prop (SSteps c s Skip s') @-}
lem_bstep_sstep :: Com -> State -> State -> BStep -> SStepsProof
  lem_bstep_sstep = undefined



