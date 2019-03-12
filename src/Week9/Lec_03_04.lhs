\begin{code}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

import Prelude hiding ((++)) 
import ProofCombinators
import BigStep
import SmallStep
\end{code}

Last lecture, we outlined some proofs talking about one small step at a time.

\begin{code}
{-@ lem_michael :: c:_ -> s:_ -> s':_ -> Prop (SStep c s Skip s') -> Prop (BStep c s s') @-}

lem_michael :: c:Com -> s:State -> s': State -> pf:SStepProof -> BStep
\end{code}

\begin{lemma}
  If $(c, s) \leadsto (\mathtt{Skip}, s')$, then $\mathtt{BigStep } c s s'
\end{lemma}

We look at two cases. The first, for the rule $\mathtt{SSeq1}$ holds easily
as $(\mathtt{Skip}; c1, s) \leadsto (\mathtt{Skip}, s')$ means that c1 must be $\mathtt{Skip}$.

The second, for the rule $\mathtt{SSeq2}$ is impossible. $\mathtt{SSeq2}$ only steps the first argument but remains a sequence.

\begin{code}
lem_michael c s s' (SSeq2 {})
  = impossible "seq-is-not-skip"
\end{code}

Then we generalize this lemma to talk about more steps.
We want to be able to talk about take more than one small step.
In fact we want to talk about 0 or more steps.
We will then show that that is equivalent to the big step semantics.
So the theorem we want to prove is
\begin{theorem}
  If $(c, s) \leadsto_{\text{0 or more}} (\mathtt{Skip}, s')$, then $\mathtt{BigStep } c s s'$.
\end{theorem}
So how do we write this "0 or more"?
Answer: It looks a lot like paths from earlier homework.
"node" from the homework corresponds to $(c, s)$.
"edge" from the homework corresponds to $(c, s) \leadsto (c', s')$.

We now define $\mathtt{SSteps}$ which we write $\leadsto^*$.

\begin{code}
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

{-
 --------------[Refl]
 (c,s) ~> (c,s)

(c,s) ~> (c',s')     (c',s') ~>* (c'', s'')
--------------------------------------------[Edge]
        (c,s) ~>* (c'',s'')
-}
\end{code}

Our theorem that small step semantics are equivalent to big step semantics then becomes
\begin{theorem}
  If $(c, s) \leadsto^{*} (\mathtt{Skip}, s')$, then $\mathtt{BigStep } c s s'$.
\end{theorem}

\begin{code}
{-@ lem_sstep_bstep :: c:_ -> s:_ -> s':_ -> Prop (SSteps c s Skip s') -> Prop (BStep c s s') @-}
lem_sstep_bstep :: Com -> State -> State -> SStepsProof -> BStep
\end{code}

-- ^ what do we do the induction on?
-- base state is c is SKIP which corresponds to Refl

lem_sstep_bstep c s s' (Refl {}) = BSkip s

lem_sstep_bstep :: Com -> State -> State -> SStepsProof -> BStep
lem_sstep_bstep c s s' (Refl {}) = BSkip s
lem_sstep_bstep (Assign {}) s s' (Edge _ _ c2 _s2 _ _ (SAssign x a _) (Refl {})) ← Refl goes here because we are allowed to assume the program path is size 1,

= BAssign x a s

           Bval b s = True    BStep (cThen s s')
       ---------------------------------------- BIfT
          BStep (If b cThen cElse) s s'


lem_sstep_bstep (If b cThen cElse) s s' (Edge _ _ _cThen _s2 _ _ (SIfT {}) c2s2_c3s3)
    -- c2s2_c3s3 :: lem_sstep_bstep cThen s s' c2s2_c3s3 is a proof that (BStep cThen s s')
= BifT b cThen cElse s s' (lem_sstep_bstep cThen s s' c2s2_c3s3)


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

What are we actually doing induction on? The path. Notice that the whileT makes the program get ``bigger'', so we cannot do induction on the program size. This makes sense, program termination is built in to these SStepsProof objects, as they are finite data structures.
So what is getting smaller?
The path is getting smaller. SSteps can only encode finite sequences of reductions. This is encoded in the statement because we -->* (Skip, s')
So we are doing induction on the length of -->*
-}

-- Similarly, the other direction
{-@ lem_bstep_sstep :: c:_ -> s:_ -> s':_ -> Prop (BStep c s s') -> Prop (SSteps c s Skip s') @-}
lem_bstep_sstep :: Com -> State -> State -> BStep -> SStepsProof
  lem_bstep_sstep = undefined



