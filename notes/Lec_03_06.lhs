Notes:

**No collaboration on final**

Q & A from Piazza:

lem_ss_det
What does c1 mean?

Recall the SSeq2 Rule:

(ca, s) -> (ca', s')
--------------------------------------
(ca; cb, s) -> (ca';cb, s')

\begin{code}
lem_ss_det c s c1 s1 c2 s2 =
           (SSeq2 cA1 cA' cB1 _ _s1 cA_s_cA'_s1)
           (SSeq2 cA2 cA'' cB2 _ _s2 cA_s_cA''_s2)
\end{code}
c == ca; cb
c1 == ca'; cb
c2 == ca''; cb

Why is cA1 == cA2??
Why is cB1 == cB2??

cA1; cB1 == cA2; cB2

What if the commands were:
c == apple; banana; canteloupe
cA1 = apple             cB1 = banana; canteloupe
cB1 = apple; canteloupe cB1 = canteloupe

then:
cA1; cB1 =/= cA2; cB2

The semi-colon defines a certain tree structure. So if they were different
commands, they would have a different parse structure.
Consequently, the two MUST be the same.

---------------------




\begin{code}
module Lec_3_6 where
import BigStep
import Expressions
\end{code}
-----------------------------------------
Floyd-Hoare Triples (Axiomatic Semantics)
-----------------------------------------
{ P } c { Q }
- P, Q are logical assertions
- c is a command
P : Precondition / assumption
Q : Postcondition / assert
What does it mean for { P } c { Q } to hold?
Let s be the starting state, and s' be the resulting state after executing c in state s
\begin{code}
{-@ type Legit P Q = s:_ -> s':_ -> { bval P s } -> (BStep c s s') -> { bval Q
s' } @-}
\end{code}
Intuitively, a triple holds if, given
- a state s
- a state s'
- a proof that P holds in state s
- a proof that c steps from state s to state s'
We can prove that Q holds in state s'
Some examples:
1) {True}
      X <~ 5
   {X = 5}
   LEGIT : we assign x to 5.
2) {X = 2}
      X <~ X + 1
   {X = 3}
   LEGIT : we simply increment x.
3) {True}
     X <~ 5;
     Y <~ 0
   {X = 5}

   LEGIT : We assign 5 to x. We could have a stronger postcondition,
   but this one is still valid.
4) {True}
      X <~ 5;
      Y <~ X
   {Y = 5}
   LEGIT : We assign 5 to x, then x to y, so after execution we have Y = 5.
5) {X = 2 && X = 3}
      X <~ 5
   {X = 0}
   LEGIT : Even though the postcondition will not hold, the precondition
   is a contradiction so it will be impossible to produce a proof that
   { X = 2 && X = 3 } in any state s.
6) {True}
      SKIP
   {False}
   NOT LEGIT : We cannot prove false.
7) {False}
      SKIP
   {True}
   LEGIT : We can prove anything assuming False, including True.
8) {True}
      WHILE True DO
        SKIP
   {False}
   LEGIT : The body of the triple is an infinite loop, so it is impossible
   to produce a corresponding BStep term. Thus, we can prove False.
9) {X = 0}
      WHILE X <= 0 DO
        X <~ X + 1
   {X = 1}
   LEGIT : The loop executes once, incrementing X.
10) {X = 1}
       WHILE not (X <= 0) DO
         X <~ X + 1
    {X = 100}
    NOT LEGIT : Another infinite loop, so we can prove any postcondition.
