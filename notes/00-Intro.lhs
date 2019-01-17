module Intro where 

What is Liquid Haskell?
=======================

Liquid Haskell:

- separate program (not part of GHC),
- parses Haskell + annotations (look like Haskell comments),
- checks program + annotations (via an external SMT solver),
- reports success or error.

If Liquid Haskell succeeds, the program is compiled normally.

More precise types
==================

The primary goal of Liquid Haskell is to add more precise types to a Haskell program, so that you can e.g.:

- prove pre- and postconditions of functions,
- establish invariants,
- prove properties of your program.

An extension of Haskell
=======================

If a program is erroneous in Haskell, it is wrong in Liquid Haskell as well:

\begin{code}
i1 :: Int
i1 = 3 -- try to replace with something that is not an Int
\end{code}

Refinement types
================

We can use set comprehension notation to refine a Haskell type signature for Liquid Haskell:

\begin{code}
{-@ i2 :: { i : Int | i >= 3 } @-}
i2 :: Int
i2 = 4

{-@ i3 :: { i : Int | i >= 3 } @-}
i3 :: Int
i3 = 2 -- fixme
\end{code}


Type synonyms
=============

We can define abbreviations in for Liquid Haskell in much the same way that we can do in Haskell:


\begin{code}
{-@ type GT3  = { i : Int | i >= 3 } @-}
{-@ type GT N = { i : Int | i >= N } @-}

{-@ i4 :: GT3 @-}
i4 :: Int
i4 = 4

{-@ i5 :: GT 3 @-}
i5 :: Int
i5 = 3
\end{code}


The type parameter must be a capital letter here! 

(Lower-case letters for "Haskell" type variables, upper-case letters for Liquid Haskell expressions.)

The Liquid Haskell Prelude defines (among other things) a convenient synonym for natural numbers.

\begin{code}
{-@ type Nat = { i : Int | i >= 0 } @-}
\end{code}

Refinement types must refine
============================

\begin{code}
{-@ i6 :: { i : Int | i == 6 } @-}
i6 :: Int -- try to replace with Integer
i6 = 6
\end{code}


One expression, many types
============================


\begin{code}
-- {-@ i7 :: { i : Int | i == 6 } @-}
-- {-@ i7 :: { i : Int | i >= 0 } @-}
-- {-@ i7 :: { i : Int | i <= 10 } @-}
-- {-@ i7 :: { i : Int | i >= 0 && i <= 10 } @-}
-- {-@ i7 :: Int @-}
i7 :: Int
i7 = 6
\end{code}

All of these work (but we have to choose one).

Refinement types and functions
==============================

\begin{code}
{-@ i8 :: { i : Int | i == 3 } @-}
i8 :: Int
i8 = 1 + 2
\end{code}

What is the type of `(+)`?

\begin{code}
{-@ plus :: a : Int -> b : Int -> { i : Int | i == a + b } @-}
plus :: Int -> Int -> Int
plus = (+)

{-@ i9 :: { i : Int | i == 3 } @-}
i9 :: Int
i9 = plus 1 2
\end{code}

The type of plus is a *dependent function type*.

Note: We can only use what we have established in the types. 

If we remove the Liquid type signature for `plus`, then `i9` 
will no longer typecheck.


Preconditions vs. postconditions
================================

A *precondition* restricts how or when we can call a function.

\begin{code}
{-@ pre :: i : Nat -> { j : Int | j >= 2 * i } -> Int @-}
pre :: Int -> Int -> Int
pre i j = j - i - i
\end{code}

A *postcondition* establishes knowledge that can be used by the system.


\begin{code}
{-@ post :: i : Int -> { j : Int | j >= 3 * i } @-}
post :: Int -> Int
post i = 3 * i
\end{code}

If we compose function calls, Liquid Haskell will check if the 
knowledge established by the postconditions implies the 
necessary preconditions (by asking an SMT solver).

\begin{code}
{-@ combine :: Nat -> Int @-}
combine :: Int -> Int
combine i = pre i (post i)
\end{code}


Once again, we can only work with what we have established 
via the types. For example, changing the type of `combine` 
to `Nat -> Nat` does not work without adapting the type of 
`pre` as well.


Integer arithmetic
==================

SMT solvers are relatively good at dealing with integers. 
Because Liquid Haskell relies on an SMT solver to do all 
the hard work, we get to benefit from that:

\begin{code}
{-@ double :: x : Int -> { i : Int | i == 2 * x } @-}
double :: Int -> Int
double x = x + x
\end{code}

\begin{code}
{-@ dist :: x : Int -> y : Int -> z : Int -> { i : Int | i == x * z + y * z } @-}
dist :: Int -> Int -> Int -> Int
dist x y z = (x + y) * z
\end{code}


Exercises
=========

1. Can you give a refined type to abs?

\begin{code}
abs :: Int -> Int
abs x
  | x < 0     = - x
  | otherwise = x
\end{code}

2. Can you fix the type signature for `sub` so that it implements 
   subtraction restricted to (suitable) natural numbers?

\begin{code}
\end{code}

3. Can you add a type signature to `halve` that captures that the sum 
   of the two components of the resulting tuple is the equal to the 
   function argument? 

\begin{code}
halve :: Int -> (Int, Int)
halve i = (j, j + r)
  where
    j = i `div` 2
    r = i `mod` 2
\end{code}

(Hint: you can use fst and snd in the refinement to access the components of the pair.)