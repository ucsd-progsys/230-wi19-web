

Week 2 - Wed
============

Remember our `sum` function from last lecture:

\begin{code}
module EquationalProofs where

import Prelude hiding (sum)

{-@ reflect sum @-}                                 
sum :: Int -> Int 
sum n = if n <= 0 
    then  0                   -- "base"      case 
    else  n + sum (n-1)       -- "recursive" case
\end{code}

This is a recursive function. Essentially it takes the body of the function and dumps it in as a postcondition. This has the effect that every time you call the function, it tells the type system/type checker “sum of 0 is defined as equal to 0.”

...and also the `assert` function:

\begin{code}
{-@ assert :: {p:Bool | p } -> a -> a @-}
assert :: Bool -> a -> a 
assert True  x = x 
assert False _ = impossible "Yikes assert failed!" 
\end{code}

-----------------------------------------

Building from last time, 

\begin{code}
tests =  [ assert (sum 0 == 0)              -- VC 1
         , assert (sum 1 == 1) 
         , assert (sum 2 == 3)
         , assert (sum 3 == 6)
         ]

\end{code}

The important thing to know is that the SMT solver doesn’t know anything about 'sum' at all. You can chain all these assertions together because they build on each other. However, if you delete one of the preceding ones, the chain breaks.

How can we make these more like proofs?

We'll develop a couple of operators that let us write the same thing, but in a simplified style.

## Proving a statement 

Suppose we want to prove that `sum 3 == 6`. We'll make a function 'theorem' that doesn't take any inputs, and produces as output a postcondition that says what we want to prove. If we can create some value such that `sum 3 == 6`, then it means it must be true. 

### Step 1

How would we create such a value? Let's say we want to prove that `1 + 3 == 4`. The SMT solver can prove math like this. We can create a refinement as follows, that runs fine. However, if you change `1 + 3 == 4` to `1 + 3 == 40`, it won't pass.

\begin{code}
{-@ theorem_orange :: {1+3 == 4} @-}
theorem_orange = ()
\end{code}

### Step 2

Let's now try proving that `sum 0 == 0`. We can start off with 

\begin{code}
{-@ theorem_stuff :: {sum 0 == 0} @-}
theorem_stuff = ()
\end{code}

but this won't pass, because we need another step to persuade the SMT solver that `sum 0 == 0`. If we can just call sum on 0, like so, it will dump out the desired postcondition for us. Side note: use `{-# LANGUAGE PartialTypeSignatures #-}`

\begin{code}
{-@ theorem_stuff :: _ -> {sum 0 == 0} @-}
theorem_stuff :: _
theorem_stuff _ = sum 0
\end{code}

### Step 3

Let's now try proving that `sum 2 == 3`. What we need to do is spell out each of the equalities.

An aside: If you want to hide warnings, you can assign something as `undefined`.

How would we do this on paper?

\begin{code}
sum 2 
	= 2 + sum 1
	= 2 + 1 + sum 0
	= 2 + 1 + 0
	= 3
\end{code}

We'd like to write something that looks like this proof, but have it typecheck. For this, we're going to use a special equality operator `(===)` that tells the system that things are equal to other things. Think of it as a binary operator that takes two things, an expression e1 and and an expression e2, and we want to check that these 2 expressions are equal to each other. What we then want to guarantee is that the postcondition is equal to both.

In more detail, this **equation combinator** is an infix operator that takes 2 arguments, x & y, and returns y. x is of whatever type a, and y is of whatever type a, but y must be equal to x (as a precondition). The output is equal to both.

\begin{code}
infixl 3 ===
{-@ (===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a
_ === y  = y
\end{code}

Now we can write things like

\begin{code}
{-@ theorem_stuff2 :: _ -> { v: _ | sum 2 == 3 } @-}
theorem_stuff2 :: _ 
theorem_stuff2 _ = sum 2 
              === 2 + sum 1 
              === 2 + 1 + sum 0
              === 2 + 1 + 0 
              === 3 
\end{code}

This works because we're unfolding the definition of `sum 2`, then `sum 1,` and `sum 0`. 

Why `===` instead of `==`?

\begin{code}
{-@ (=*=) :: x:a -> y:{a | y == x} -> {v:Bool | x == y} @-}
(=*=) :: (Eq a) => a -> a -> Bool 
(=*=) x y = x == y
\end{code}

This would not work because you cannot chain equivalence. Instead this is the Boolean test, which returns a type `Bool`. `===` returns the same value, which is why we can chain the equalities like this.

This is like saying

\begin{code}
anilTests :: _
anilTests =  
    [ assert (sum 2 == 2 + sum 1)
    , assert (sum 1 == 1 + sum 0)
    , assert (sum 0 == 0)
    ]
\end{code}

Even if you delete `assert (sum 1 == 1 + sum 0)`, `assert (sum 2 == 2 + sum 1)` will still pass because sum 2 and 2 + sum 1, from the position of the SMT solver, are asking the same question. SMT solver can solve this without knowing exactly what sum 2 or sum 1 are equal to.

### Step 4

Now we will finally prove `sum 3 == 6`.
We could prove it the same way as `sum 2 == 3`, but the proofs are mostly the same. How can we reuse that proof?

We'll use the **because combinator**, `?`. This lets you "add" some fact into a proof term. It takes two arguments, `x ? coz` and just gives you back `x`. The second argument is just some fact, and all we're doing is reminding the SMT solver of it.

\begin{code}
{-@ another_theorem :: _ -> { v: _ | sum 3 == 6 } @-}
another_theorem :: _ 
another_theorem _ = sum 3 
                === 3 + sum 2 
                	? theorem_stuff2 ()
                === 6
\end{code}

We want to remind `another_theorem` of what we have already proven. Now we can call the function/lemma `theorem_stuff` to tell the solver that sum 2 is equal to 3. 

## Proving something for all n

What if we wanted to prove something like `for all n, n <= sum n`?

It would look something like 

\begin{code}
{-@ theorem_MJ :: n:Int -> { n <= sum n} @-}
theorem_MJ :: Int -> _ 
theorem_MJ 0 = undefined
\end{code}

The proof of this theorem is some function, that we have to write, that takes as input any n. This is left as an exercise. 
