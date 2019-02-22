\documentstyle{article}

\begin{document}

\begin{code}
module Lex_02_13 where
\end{code}

CSE 230: Programming Languages
==============================

Wednesday, February 13 (Lecture 14)
-----------------------------------

\section{Termination Example}

- "Non-decreasing parameter" can mean:
  - Not doing structural recursion.
    - i.e. making a recursive call stripping away one layer of a parameter.
  - Can rewrite the function, or
    - make a size measure.

`lsize'` passes on structural termination checking alone.

`lsize1` passes as LH falls back on a measure defined in its Prelude.

\begin{code}
-- ok
lsize' :: [a] -> Int
lsize' [] = 0
lsize' (x:xs) = 1 + lsize' xs

-- ok
lsize1 :: [a] -> Int
lsize1 [] = 0
lsize1 [_] = 1
lsize1 (x:y:zs) = 2 + lsize1 zs
\end{code}

With a custom List type that does not have any measures, `lsize2` will be
rejected by the termination checker. A copy of it, `silly`, is okay when we 
supply a termination metric.

A note on `measure`: Think of a measure as a special class of 
reflects with magical powers.

\begin{code}
data List a
    = Nil
    | Cons a (List a)

-- termination check fails
lsize2 :: List a -> Int
lsize2 Nil = 0
lsize2 (Cons _ Nil) = 1
lsize2 (Cons x (Cons y zs)) = 1 + lsize2 (Cons x zs)

{-@ measure lsize @-}
{-@ lsize :: List a -> Nat @-}
lsize :: List a -> Int
lsize Nil        = 0
lsize (Cons x xs) = 1 + lsize xs

{-@ silly :: xs:List a -> Int / [lsize xs] @-}
silly :: List a -> Int
silly Nil = 0
silly (Cons _ Nil) = 1
silly (Cons x (Cons y zs)) = 1 + silly (Cons x zs)

\end{code}

\begin{code}
data AExp
    = N Int 
    | V String
    | Plus AExp AExp

{-@ measure asize @-}
{-@ asize :: AExp -> Nat @-}
asize :: AExp -> Int
asize (N _) = 1
asize (V _) = 1
asize (Plus l r) = 1 + asize l + asize r
\end{code}

Here, using `[asize a2]` for termination will not work, as the following
does not decrease in `a2`. What we instead wish to show is that at every 
step, we are decreasing in at least one parameter.

A fancy word for this is decreasing "lexicographic", that is, like in a 
dictionary. That is, sort by the first character, then tiebreak with the second,
and so on... (aaa < aab < baa).

```
merge_exps (Plus (V x) a1') a2 = Plus (V x) (merge_exps a1' a2)
```

For some reason `[2 * (asize a2) + asize a1]` works, 
whereas `[asize a1 + asize a2]` does not.

\begin{code}
{-@ merge_exps :: a1:AExp -> a2:AExp -> AExp / [2 * (asize a2) + asize a1] @-}
merge_exps :: AExp -> AExp -> AExp
merge_exps (N n1) (N n2) = N (n1 + n2)
merge_exps (V x1) (V x2) = Plus (V x1) (Plus (V x2) (N 0))
merge_exps (V x) (N n) = Plus (V x) (N n)
merge_exps (N n) (V x) = Plus (V x) (N n)
merge_exps (N n) a2 = merge_exps a2 (N n)
merge_exps (V x) a2 = merge_exps a2 (V x)
merge_exps (Plus (V x) a1') a2 = Plus (V x) (merge_exps a1' a2)
merge_exps (Plus _ _) _ = N 0

\end{code}

\section{Termination Example 2}

\begin{code}

type Vname = String

{-@ data Pred [psize] @-}
data Pred 
  = Var Vname           -- ^ x, y, z    variables 
  | Not Pred            -- ^ ~ p        negation
  | Or  Pred Pred       -- ^ p1 \/ p2   disjunction
  | And Pred Pred       -- ^ p1 /\ p2   conjunction
  deriving (Show)

{-@ measure psize @-}
{-@ psize :: Pred -> Nat @-}
psize :: Pred -> Int
psize (Var _) = 1
psize (Not p) = 1 + psize p
psize (Or  p q) = 1 + psize p + psize q
psize (And p q) = 1 + psize p + psize q

{-@ nnf :: p:Pred -> NNF @-}
nnf :: Pred -> Pred
nnf (Not (And p1 p2)) = Or (nnf (Not p1)) (nnf (Not p2))
nnf (Not (Or p1 p2)) = And (nnf (Not p1)) (nnf (Not p2))
nnf p = p

\end{code}

\section{Back to Imperative Programming!}

Previous rules go here...

BStep c s1 s2

  bval b s = TRUE      BStep c1 s s'
------------------------------------- [BIfT]
  BStep (If b c1 c2) s s'


  bval b s = FALSE      BStep c1 s s'
------------------------------------- [BIfF]
  BStep (If b c1 c2) s s'


Last covered, not sure if working...

  bval b s = TRUE      BStep c s s1     BStep (While b c) s1 s'
---------------------------------------------------------------- [BWhileT]
  BStep (While b c) s s'


Base case:

  bval b s = FALSE
------------------------- [BWhileF]
  BStep (While b c) s s


We will only be interested in finite proof-trees, i.e. where loops iterate 
finite numbers of times. 


-- \end{document}