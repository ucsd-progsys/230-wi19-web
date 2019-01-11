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
list3 = 1 `Cons` 2 `Cons` 3 `Cons` Nil -- not ok
\end{code}


\begin{code}
{-@ fib :: Nat -> Int @-}
fib :: Int -> Int
fib 0 = 0 
fib 1 = 1
fib i = fib (i-1) + fib (i-2)
\end{code}

fib 2 ==> fib 1 + fib (-1)
- i-3 badness
- sequence eventually hitting 0 1



\begin{code}
{-@ range :: lo:Int -> hi:Int -> List Int / [hi - lo] @-} 
range :: Int -> Int -> List Int
range lo hi
  | lo < hi   = Cons lo  (range (lo+1) hi)
  | otherwise = Nil 
\end{code}

\begin{code}

-- type Nat = {v:Int | 0 <= v}

{-@ ack :: m:Nat -> n:Nat -> Nat / [m, n] @-}
ack :: Int -> Int -> Int
ack m n
  | m == 0    = n + 1
  | n == 0    = ack (m-1) 1
  | otherwise = ack (m-1) (ack m (n-1))
\end{code}



\begin{code}
{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil           = 0
length (x `Cons` xs) = 1 + length xs

{-@ measure length @-}

{-@ data List [length] @-} 

\end{code}

\begin{code}
map :: (a -> b) -> List a -> List b
map _ Nil           = Nil
map f (x `Cons` xs) = f x `Cons` map f xs
\end{code}


\begin{code}
{-@ interleave :: xs:List a -> ys:List a -> List a / [length xs + length ys] @-}
interleave :: List a -> List a -> List a
interleave Nil           ys  = ys
interleave xs            Nil = xs
interleave (x `Cons` xs) ys  = x `Cons` interleave ys xs
\end{code}