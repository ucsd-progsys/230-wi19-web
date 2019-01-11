\begin{code}
{-@ LIQUID "--no-structural" @-}
module Lists where 

import Prelude hiding (repeat, map, length, head, take, drop)
\end{code}


Goal
====

In order to see some more interesting examples of refinements, 
let's look at a data structure we're all familiar with: lists.

Let's look at some typical functions on lists and see how their 
type can be improved.

Our own list type
=================

Built-in lists and the functions on these already have a lot of 
predefined features in Liquid Haskell. 

To better understand how to define datatypes in Liquid Haskell 
and establish properties on them, let us work with our own lists:

\begin{code}
data List a = Nil | Cons a (List a)
  deriving (Show)

infixr 5 `Cons`
\end{code}

In principle, we can use these lists immediately in Liquid Haskell:

\begin{code}
list1 :: List Int
list1 = 1 `Cons` 2 `Cons` 3 `Cons` Nil
\end{code}

And we can even use them with refinement types:

\begin{code}
{-@ list2 :: List Nat @-}
list2 :: List Int
list2 = 1 `Cons` 2 `Cons` 3 `Cons` Nil -- ok

{-@ list3 :: List Nat @-}
list3 :: List Int
list3 = -1 `Cons` 2 `Cons` 3 `Cons` Nil -- not ok
\end{code}


Termination
===========

However, if we try to define even a very simple recursive function, we get an error: 
  
\begin{code}
{-@ fib :: i:Int -> Int  @-}
fib :: Int -> Int
fib i | i == 0    = 0 
      | i == 1    = 1 
      | otherwise = fib (i-1) + fib (i-2)
\end{code}

**Q:** Why is there an error? 

Proving Termination with Metrics 
================================

(c.f. Turing!)

Liquid Haskell checks that there is some "well-founded decreasing metric" at each recursive call:

- Non-negative 
- Value at each call gets _strictly_ smaller at each recursive call


**Default:** the first `Int`-valued argument.

Q: How can we fix `fib` so it checks?

User specified Termination Metrics
================================

The first integer is not always decreasing!

\begin{code}
{-@ range :: lo:Int -> hi:Int -> [Int] @-} 
range :: Int -> Int -> [Int]
range lo hi
 | lo < hi = lo : range (lo+1) hi
 | otherwise = []
\end{code}

Q: Can you think of what metric _is_ decreasing?

Lexicographic Termination
=========================

Q: (Why) does Ackermann's function terminate?

\begin{code}
{-@ ack :: m:Int -> n:Int -> Int @-} 
ack :: Int -> Int -> Int
ack m n
  | m == 0 = n + 1
  | n == 0 = ack (m-1) 1
  | otherwise = ack (m-1) (ack m (n-1))
\end{code}


Terminating functions on data types
===================================

Now, lets try to define a function over lists, we get an error:

\begin{code}
{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil           = 0
length (x `Cons` xs) = 1 + length xs
\end{code}

Liquid Haskell tried to prove *termination* of all functions, 
but for user-defined datatypes, we have to teach it how to do this.

Measures
========

We can declare `length` to be a measure by saying

\begin{code}
-- {-@ measure length @-} -- uncomment this
\end{code}

and then declaring that length is the termination measure to use for the List type:

\begin{code}
-- {-@ data List [length] @-} -- uncomment this
\end{code}

A measure is a single-argument function with one case per constructor. 
Measures are lifted into the types of the constructors of the function, 
and can then also be used in refinements:

    Nil   ::  { ys : List a | length ys == 0 }
    Cons  ::  a -> xs : List a -> { ys : List a | length ys == 1 + length xs }

With these declarations in place, length now type- and termination-checks.


Mapping
=======

The following definition of map now also termination-checks, because 
Liquid Haskell will assume that the function decreases the termination 
measure of its first "structured" argument:

\begin{code}
map :: (a -> b) -> List a -> List b
map _ Nil           = Nil
map f (x `Cons` xs) = f x `Cons` map f xs
\end{code}

Can you add a type signature that captures that map does not change the length of the input list?

Interleaving two lists
======================

Termination is less obvious for interleave:

\begin{code}
interleave :: List a -> List a -> List a
interleave Nil           ys  = ys
interleave xs            Nil = xs
interleave (x `Cons` xs) ys  = x `Cons` interleave ys xs
\end{code}


In the recursive call, it is not clear that ys is shorter than x : xs.

(Why) *does* the above function "terminate"? Can you think of something that always "decreases"? 

Can you further refine the type signature such that we track the length of the resulting list?

Disabling termination checking
==============================

Termination checking can be disabled for a whole file using the `--no-termination option`.

Termination checking can be disabled for an individual function by using the `lazy` directive.

\begin{code}
repeat :: a -> List a
repeat x = x `Cons` repeat x
{-@ lazy repeat @-}
\end{code}

Disabling termination checking can be a useful test, because quite often, 
termination errors are not easily recognisable as termination errors.

Totality
========

Liquid Haskell also checks totality, i.e., if a function covers all possible cases:

\begin{code}
head :: List a -> a
head (Cons x xs) = x
\end{code}

Can you provide a refinement type such that this function passes the totality check?

Impossible cases
================

The definition of head above has the disadvantage that it still triggers a warning in Haskell.

We can fix this by defining:

\begin{code}
{-@ impossible :: { s : String | False } -> a @-}
impossible :: String -> a
impossible msg = error msg
\end{code}

The precondition of impossible is indeed impossible. So Liquid Haskell will verify that it cannot be called.

Fix this definition that now passes the totality check, but fails due to the Liquid Haskell type of `impossible`:

\begin{code}
tail :: List a -> List a
tail (Cons x xs) = xs
tail Nil         = impossible "tail: Nil"
\end{code}

Exercise: Taking elements out of a list
=======================================

Why does the following definition of take not typecheck? Can you fix it?

\begin{code}
-- {-@ take :: i : Nat -> List a -> { ys : List a | length ys == i } @-}
take :: Int -> List a -> List a
take _ Nil         = Nil
take 0 _           = Nil
take i (Cons x xs) = x `Cons` take (i - 1) xs
\end{code}

Could you use impossible in the definition of take?

Exercise: Dropping elements from a list
=======================================

Also provide a proper refinement type for `drop n xs` which "removes"
the first `n` elements of a list:

\begin{code}
drop :: Int -> List a -> List a
drop _ Nil         = Nil
drop 0 xs          = xs
drop i (Cons _ xs) = drop (i - 1) xs
drop _ _           = impossible "drop"
\end{code}

Exercise: Sublist 
================

This function computes the sublist of `l` elements starting at position `s` 

\begin{code}
sublist :: Int -> Int -> List a -> List a
sublist s l xs = take l (drop s xs)
\end{code}

Let's test that this works:

\begin{code}
testSublist1 :: List Int
testSublist1 = sublist 1 2 (1 `Cons` 2 `Cons` 3 `Cons` 4 `Cons` Nil) -- ok

testSublist2 :: List Int
testSublist2 = sublist 2 3 (1 `Cons` 2 `Cons` 3 `Cons` 4 `Cons` Nil) -- should fail
\end{code}