\documentclass{article}
\usepackage{latexsym, tikz-cd, minted, parskip}
\usetikzlibrary{decorations.pathmorphing}
\newminted[code]{haskell}{}
\newmintinline[inlinecode]{haskell}{}

\begin{document}

\begin{code}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--short-names" @-}
{-# LANGUAGE GADTs #-}

module Lec_03_01 where

import ProofCombinators
import Expressions
import Imp
import BigStep
import SmallStep
import qualified State as S
\end{code}

\section{Introduction}

We're continuing small-step semantics today. Recall the form of small-step
semantics: \[(c, s) \leadsto (c', s'),\] where \((c, s)\) is a ``configuration''
made up of a command \(c\) and a state \(s\). We represent this in Haskell code
as \inlinecode{(SStep c s c' s')}.

Today we want to prove two properties about our small-step semantics:
\begin{enumerate}
  \item Our semantics is \emph{deterministic}: if \((c, s) \leadsto (c_1, s_1)\)
    and \((c, s) \leadsto (c_2, s_2)\), then \(c_1 = c_2\) and \(s_1 = s_2\).

    \begin{tikzcd}[row sep=0]
      & (c_1, s_1) \arrow[dd, equal]\\
      (c, s) \arrow[ru, squiggly] \arrow[rd, squiggly] & \\
      & (c_2, s_2)
    \end{tikzcd}
  \item Our small-step semantics is in some sense equivalent to our big-step
    semantics. Why is this hard?
    \begin{itemize}
      \item We have to talk about the ``final state'' in our small-step
        semantics, which means
      \item we have to somehow describe executing the ``entire program''.
    \end{itemize}
\end{enumerate}

Last time, we started on these goals by proving that \((\texttt{Skip}, s)\) can't
step to any other configuration:
\begin{code}
{-@ lem_not_skip :: c:_ -> c':_ -> s:_ -> s':_ ->
      Prop (SStep c s c' s') -> {c /= Skip} @-}
lem_not_skip :: Com -> Com -> State -> State -> SStep -> Proof
lem_not_skip = undefined
\end{code}

\section{Our small-step semantics is deterministic}

Let's phrase this property in Liquid Haskell:

\marginpar{In class, we wrote this function returning \inlinecode{()}, not
  \inlinecode{Proof}. This is fine, however, because \inlinecode{Proof} is just
  a type alias for \inlinecode{()}.}
\begin{code}
{-@ lem_ss_det :: c:_ -> s:_ -> c1:_ -> s1:_ -> c2:_ -> s2:_ ->
      Prop (SStep c s c1 s1) ->
      Prop (SStep c s c2 s2) ->
      {c1 == c2 && s1 == s2} @-}
lem_ss_det :: Com -> State -> Com -> State -> Com -> State ->
      SStep -> SStep -> Proof
\end{code}

Now, we can split cases on the different small-step proofs.

In the \inlinecode{SAssign} case:
\begin{code}
lem_ss_det c s c1 s1 c2 s2 (SAssign {}) (SAssign {})
\end{code}
we know that
\begin{itemize}
  \item \inlinecode{c == Assign x a},
  \item \inlinecode{c1 == c2 == Skip}, and
  \item \inlinecode{s1 == s2 == asgn x a s}.
\end{itemize}
So we can rely on Liquid Haskell to just figure out the proof for us:
\begin{code}
  = ()
\end{code}

Similarly, in the \inlinecode{SSeq1} case:
\begin{code}
lem_ss_det c s c1 s1 c2 s2 (SSeq1 {}) (SSeq1 {})
\end{code}
we know that
\begin{itemize}
  \item \inlinecode{c == Seq Skip c'},
  \item \inlinecode{c1 == c2 == c'}, and
  \item \inlinecode{s1 == s2 == s}.
\end{itemize}
Again this is is enough for Liquid Haskell to figure the proof out:
\begin{code}
  = ()
\end{code}

The \inlinecode{SSeq2} case is more complex:
\begin{code}
lem_ss_det c s c1 s1 c2 s2
  (SSeq2 cA cA1 cB _s _s1 cA_s_cA1_s1)
  (SSeq2 _  cA2 _  _  _s2 cA_s_cA2_s2)
\end{code}
Here, we know
\begin{itemize}
  \item \inlinecode{c == Seq cA cB},
  \item \inlinecode{c1 == Seq cA1 cB}, and
  \item \inlinecode{c2 == Seq cA2 cB}, as well as
  \item \inlinecode{cA_s_cA1_s1} (that is, \((cA, s) \leadsto (cA1, s1)\)), and
  \item \inlinecode{cA_s_cA2_s2} (\((cA, s) \leadsto (cA2, s2)\)).
\end{itemize}

We need to prove that \inlinecode{c1 == c2 && s1 == s2}, which simplifies to
proving \inlinecode{cA1 == cA2 && s1 == s2}. To do this, we can use
\inlinecode{lem_ss_det} inductively:
\begin{code}
  = lem_ss_det cA s cA1 s1 cA2 s2 cA_s_cA1_s1 cA_s_cA2_s2
\end{code}

Now for the \inlinecode{SWhileT} case:
\begin{code}
lem_ss_det c s c1 s1 c2 s2
  (SWhileT b  body  _s)
  (SWhileT _b _body _)
\end{code}
We know here that
\begin{itemize}
  \item \inlinecode{c1 == c2 == Seq body (While b body)} and
  \item \inlinecode{s1 == s2 == s}.
\end{itemize}
This is exactly what we need, so Liquid Haskell proves this case automatically:
\begin{code}
  = ()
\end{code}

The \inlinecode{SWhileF}, \inlinecode{SIfT}, and \inlinecode{SIfF} cases are
similar and can all be proven automatically:
\begin{code}
lem_ss_det c s c1 s1 c2 s2 (SWhileF {}) (SWhileF {}) = ()
lem_ss_det c s c1 s1 c2 s2 (SIfT {}) (SIfT {}) = ()
lem_ss_det c s c1 s1 c2 s2 (SIfF {}) (SIfF {}) = ()
\end{code}

We've handled all of the constructors for \inlinecode{SStep}. Are we done?
Liquid Haskell doesn't think so:

\begin{verbatim}
Error: Liquid Type Mismatch

 103 | lem_ss_det c s c1 s1 c2 s2 (SAssign {}) (SAssign {})
       ^^^^^^^^^^

   Inferred type
     VV : {v : GHC.Prim.Addr# | v == "function lem_ss_det"}

   not a subtype of Required type
     VV : {VV : GHC.Prim.Addr# | 5 < 4}
\end{verbatim}

As we've seen before, this error means we're missing a case. But what case?
Recall that we divided the cases where \inlinecode{c == Seq cA cB} into cases
where both proofs are either \inlinecode{SSeq1} or \inlinecode{SSeq2}. But what
if one is \inlinecode{SSeq1} and the other is \inlinecode{SSeq2}?
\begin{code}
lem_ss_det c s c1 s1 c2 s2
  (SSeq1 {})
  (SSeq2 cA cA' cB2 _s _s2 cA_s_cA'_s2)
\end{code}

Here, the first proof tells us that \inlinecode{c == Seq Skip cB1}, while the
second proof tells us that \inlinecode{c == Seq cA cB2}. So we know that
\inlinecode{cA == Skip} and \inlinecode{cB1 == cB2}. However, the second proof
also tells us that \((cA, s) \leadsto (cA', s2)\), that is, that
\((\texttt{Skip}, s) \leadsto (\texttt{Skip}, s2)\). We know that this is
impossible: we proved that last class. We can thus dismiss this case by using that theorem:
\begin{code}
  = impossible ("Skip can't step" ? lem_not_skip cA cA' s s2 cA_s_cA'_s2)
\end{code}

Finally, we need the opposite case, where the first proof is \inlinecode{SSeq2}
and the second is \inlinecode{SSeq1}:
\begin{code}
lem_ss_det c s c1 s1 c2 s2
  (SSeq2 cA cA' cB1 _s _s1 cA_s_cA'_s1)
  (SSeq1 {})
  = impossible ("Skip can't step" ? lem_not_skip cA cA' s s1 cA_s_cA'_s1)
\end{code}

\section{Our small- and big-step semantics are equivalent}

How can we go from our small-step semantics to ``executing whole program''? We
want to say that if \[(c, s) \leadsto (c_1, s_1) \leadsto (c_2, s_2) \leadsto \cdots
  \leadsto (\texttt{Skip}, s'),\] then \[c : s \Rightarrow s'\] (and vice-versa).

One idea (from Michael): work backward. First, we prove that if \[(c_n, s_n)
  \leadsto (\texttt{skip}, s'),\] then \[c_n: s_n \Rightarrow s'.\] That is, we
prove our semantics is correct when it only needs to take a single step. Once
we've proved this, we proceed inductively. We prove that if \[(c_{n - 1}, s_{n -
    1}) \leadsto (c_n, s_n),\] then \[c_{n - 1}: s_{n - 1} \Rightarrow s'.\]

Let's try to prove this first lemma. Phrased in Liquid Haskell, we have
\begin{code}
{-@ lem_michael :: c:_ -> s:_ -> s':_ ->
      Prop (SStep c s Skip s') -> Prop (BStep c s s') @-}
lem_michael :: Com -> State -> State -> SStep -> BStep
\end{code}

We case split on the small-step proof. Let's start with the \inlinecode{SAssign} case:
\begin{code}
lem_michael c s s' (SAssign x a _s)
\end{code}
Here we know that
\begin{itemize}
  \item \inlinecode{c == Assign x a s} and
  \item \inlinecode{s' == asgn x a s}.
\end{itemize}

We only have one way to produce a big-step proof for an assignment statement, so
we can just use that:
\begin{code}
  = BAssign x a s
\end{code}

We'll look at the rest of the cases on Monday.
\begin{code}
lem_michael c s s' cs_skips' = undefined
\end{code}
\end{document}
% Local Variables:
% TeX-command-extra-options: "-shell-escape"
% TeX-master: t
% End:
