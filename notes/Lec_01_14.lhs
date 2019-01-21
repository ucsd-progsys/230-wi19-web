\begin{code}

-- module Lec_01_14 where 
-- import           Prelude hiding (lookup)

{-@ impossible :: { s : String | False } -> a @-}
impossible :: String -> a
impossible msg = error msg
\end{code}

Assertions
==========

Assert statement: a statement that takes a predicate `assert (p)` and checks whether it holds at that point in the program. If the predicate is evaluated to false, the `assert` statement fails, and the program throws an exception.

The function `assert` can be defined in Haskell, like:

\begin{code}
assert :: Bool -> a -> a
assert True x = x
assert False _ = undefined impossible "Yikes assert failed!"

test1 = assert True  -- always passes
-- test2 = assert False -- always fails, and stops the execution
\end{code}

Without any refinement, the `assert False _` case is reachable. To fix this we need to refine 'assert' such that it can only be called with a precondition `True`.

\begin{code}
{-@ assert1 :: {p:Bool | p} -> a -> a @-}
assert1 :: Bool -> a -> a
assert1 True x = x
-- assert1 False _ = impossible "Yikes assert1 failed!"

test3 = assert1 True  -- always passes
-- test4 = assert1 False -- always fails, and stops the execution
\end{code}

Let's look at another example
\begin{code}
test5 = assert (1 < 10)
\end{code}

This assert generates a verification condition: given `t = (1<10)`, can we prove that `t` is true? because the precondition in the refinement type of assert constrains `t` to be true.

In other words,
```
let t = 1 < 10
    in (assert t)
t = (1 < 10) => t
```

\begin{code}
test6 x = assert (x < x - 1)  -- fails because we can't prove x /\ t = (x < x - 1) => t
test7 x = assert (x < x + 1)  -- passes.

{-@ lazy mj @-}
mj :: Int -> Int -> Int
mj x 0 = 1
mj x n = x * mj x (n-1)

test8 x = assert (x < mj x 1)

\end{code}

In case of the mj function, SMT solver fails to verify the assertion because it can't reason about mj using the given type specifications. mj needs to be decorated with refinement types since SMT solver only keeps track of refinements.
Note : The `lazy` directive indicates that the termination checker has been disabled.

Let's look at another example of the function `plus`-

\begin{code}
plus :: Int -> Int -> Int
plus x y = x + y

test9 x = assert (x < plus x 1)
\end{code}

Similar to the reasoning we used for mj, SMT solver can not detect plus until we add the following refinement type for it.

\begin{code}
{-@ plus :: x:_ -> y:_ -> {v:Int | v = x + y} @-}
\end{code} 

Now we define the sum function -

\begin{code}
sum :: Int -> Int
sum n = if n <= 0 
            then 0                  -- base case
            else n + sum (n - 1)    -- recursive case

test10 n = assert (sum n <= sum (n+1))
\end{code}

The assert in test10 gives an error because the only information we have about sum is that it returns a random integer.

Basically we want to show two properties about sum 
-- sum 0 == 0
-- sum n >= 0

The second condition indicates that the post condition of `sum` should be a Nat type like so

\begin{code}
{-@ sum :: Int -> Nat @-}
\end{code}

The type signature below satisfies both the properties mentioned about sum.

\begin{code}
{-@ sum :: n:Int -> {out = (if n == 0 then 0 else out)} @-}
\end{code}

Another way of writing this is using logical implication -

\begin{code}
{-@ sum :: n:Int -> {(n != 0) || (out == 0)} @-}
{-@ sum :: n:Int -> {(n == 0) => (out == 0)} @-}
\end{code}

This type signature for sum passes `assert (sum 0 == 0)` but still fails for the following two asserts.

\begin{code}
testRJ = assert (sum 1 == 1)
testBOB = assert (sum 3 == 6)
\end{code}

The asserts fail because we are still not reasoning about the case n > 0.

It might be tempting to define the type for sum in the following manner - 

\begin{code}
{@- sum :: n:Int -> { out : Nat | out = if (n <= 0) then 0 else n + sum (n-1))}}
\end{code}

However the SMT solver can not parse this since it does not know about the function sum!

In order to get around this issue, we define sum to be an `uninterpreted function`. An uniterpreted function f obeys the axiom
x1 = x2 => f x1 = f x2

Instead of putting the whole definition of sum in the refinement type, we can use
{-@ reflect sum @-}

Substituting the n == 0 case in the type signature for sum, we get :
v == if 0 <= 0 then 0 else 0 + sum (0-1) ==> v == 0
v == if True then 0 else 0 + sum (0-1) ==> v == 0
v == 0 ==> v == 0

For the the n == 1 case :
v == if 1 <= 0 then 0 else 1 + sum (1-1) ==> v == 0
v == if False then 0 else 1 + sum (1-1) ==> v == 0
v == 1 + sum (0) ==> v == 0

Here it fails because the SMT solver does not know the value of sum (0).

After considering both assertions together it succeeds -

\begin{code}
tests = [ assert (sum 0 == 0),
		  assert (sum 1 == 1)]
\end{code}

Here's what's happening:
   (v0 == if 0 <= 0 then 0 else 0 + sum (0-1))
&& (v1 v == if 1 <= 0 then 0 else 1 + sum (1-1)==> v == 1)

We are taking a conjunction of the verification conditions of both the asserts. The assert (sum 1 == 1)
takes the value for sum(0) from the previous assert and hence passes!