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

-- ^ What do we do the induction on? Answer: the path---it's the only thing that
gets shorter (recall WHILE loops). Paths are defined inductively, and the only
thing we can case on is the FIRST step (look at definition of path).
The base case is $c = \mathtt{Skip}$ corresponding to $\mathtt{Refl}$

\begin{code}
lem_sstep_bstep c s s' (Refl {}) = BSkip s
\end{code}

These are some of the inductive cases. Notice the cases on the Edge's
parameters.
\begin{code}
lem_sstep_bstep (Assign {}) s s' (Edge _ _ c2 _s2 _ _ (SAssign x a _) (Refl {}))
  = BAssign x a s
\end{code}

The two $\mathtt{If}$ cases are similar.
Here are the big step semantics for an If:

    Bval b s = True    BStep (cThen s s')
---------------------------------------- BIfT
     BStep (If b cThen cElse) s s'
\begin{code}

lem_sstep_bstep (If b cThen cElse) s s' (Edge _ _ _cThen _s2 _ _ (SIfT {}) c2s2_c3s3)
  -- lem_sstep_bstep cThen s s' c2s2_c3s3 is a proof that (BStep cThen s s')
  = BifT b cThen cElse s s' (lem_sstep_bstep cThen s s' c2s2_c3s3)
\end{code}

IfF basically the same
\begin{code}
lem_sstep_bstep (If b cThen cElse) s s' (Edge _ _ _cThen _ _ _ (SIfF {}) c2s2_c3s3)
  = BIfF b cThen cElse s s' (lem_sstep_bstep cElse s s' c2s2_c3s3)
\end{code}

-- Similarly, we can prove the other direction; that bigstep implies smallstep.
{-@ lem_bstep_sstep :: c:_ -> s:_ -> s':_ -> Prop (BStep c s s') -> Prop (SSteps c s Skip s') @-}
lem_bstep_sstep :: Com -> State -> State -> BStep -> SStepsProof
  lem_bstep_sstep = undefined

