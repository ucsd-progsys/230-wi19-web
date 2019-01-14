
\begin{code}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--short-names" @-}
module ReasoningAboutFunctions where 

import Prelude hiding (sum, assert)
import ProofCombinators
\end{code}

Recall: Impossible 
================== 

```
{-@ impossible :: {v:_| False} -> a @-}
impossible = error
```

Assertions
==========

Lets use `impossible` to write a function `assert` such that:

* `assert True x`  returns `x` 
* `assert False x` throws an exception

\begin{code}
{-@ assert     :: {v:Bool | v} -> a -> a @-}
assert True  x = x
assert False _ = impossible "Yikes: assert fails!" 
\end{code}

Exercise
========

How can we we specify a type for `assert` that guarantees 
it will _never_ call impossible? Does your spec allow the 
below to be verified?

\begin{code}
test1   :: Int -> () 
test1 x = assert (x < x + 10) ()
\end{code}


SMT is Awesome for Decidable Specifications
===========================================

Here's a function that computes `1 + 2 + ... + n`

\begin{code}
sum :: Int -> Int 
sum n = if n <= 0 
          then  0                   -- "base"      case 
          else  n + sum (n-1)       -- "recursive" case
\end{code}

Lets check that it always returns a non-negative value:

\begin{code}
test2 :: () 
test2 = assert (0 <= sum 3) ()
\end{code}

Exercise
========

Why can't LH prove the `assert` inside `test2`? 

Can you fix the code or spec to make it pass?  


SMT is Awesome for Decidable Specifications
===========================================

LH verifies the above code by generating two *Verification Conditions (VCs)* 

* "base"  case: `(n <= 0) => (v == 0) => (0 <= v)`
* "recur" case: `(n  > 0) => (0 <= sum (n-1)) => (v = n + sum (n-1)) => (0 <= v)`

The SMT solver understants the **theory of arithmetic** `+`, `<=` etc. 

Hence, the solver can automatically check the above VCs.

Similarly, for `test2` it generates the VC 

* `(0 <= sum 3)  =>  b == (0 <= sum 3)  =>  b`

which can also be checked by the SMT solver.

(We will study VCs and how LH generates them in detail at the _end_ of the quarter.)


SMT sucks for User-Defined Functions 
====================================

What if we want to write specs over things *other than* `+` or `-` or `<=` ?!

For example, what if we want to check:

\begin{code} 
test3 = assert (sum 3 == 6)
\end{code}

Exercise 
========

**Exercise** What should we write as a spec for `sum`? 

Step 1: Declare an Uninterpreted Function 
=========================================

Lets tell LH that we want to *talk about* `sum` inside specifications. 

\begin{code}
-- {-@ measure sum :: Int -> Int @-}
\end{code}

An uniniterpreted function `f` is one where the ONLY thing the SMT solver knows is 

    forall x1, x2. (x1 == x2) => f x1 == f x2

That is, we SMT knows nothing about `f` except equal inputs yield equal outputs.

Q: Is this enough to prove that `sum 0 == 0`? 

Step 2: Reflect the Implementation
==========

Ok, lets tell LH about how `sum` behaves.

\begin{code}
-- {-@ sum :: n:Int -> {v:Int | v == (if n <= 0 then 0 else (n + sum(n-1))) } @-}

{-@ reflect sum @-}
\end{code}


Q: Is this enough to prove that `sum 0 == 0`? 

\begin{code}
test4 = assert (sum 0 == 0)
\end{code}

Why? Lets look at the VC: 

The above is equivalent to:

    assert (let t = sum 0 in t == 0)

which yields the VC 

    (t == if 0 <= 0 then 0 else n + sum (0 - 1)) => (b = (t == 0)) => b 

which the SMT solver simplifies ... because it understands 0 <= 0 is true ... to 

    (t == 0) => (b == (t == 0)) => b 
    
which is valid.

But what if we want to prove 

\begin{code}
test5 = assert (sum 1 == 1)
\end{code}

The above is equivalent to:

    assert (let t = sum 1 in t == 1)

which yields the VC 

    (t == if 1 <= 0 then 0 else n + sum (1 - 1)) => (b = (t == 1)) => b 

which the SMT solver simplifies ... because it understands 1 <= 0 is false ... to 

    (t == 1 + sum 0) => (b == (t == 1)) => b 

Now you and I know the above is valid, but **SMT does not** because `sum` is uninterpreted! 

How to tell SMT about `sum 0` ?
===============================

We need to _tell_ SMT the definition of `sum 0`...

... by *calling* `sum 0` inside our code! 

That has the effect of attaching the "postcondition" to the output of `sum 0`

\begin{code}
test5' = [ assert (sum 0 == 0) ()
         , assert (sum 1 == 1) () 
         , assert (sum 2 == 3) () 
         , assert (sum 3 == 6) () 
         ] 
\end{code}

To see why, lets look at the VCs! 

        (sum 0 == if 0 <= 0 then 0 else 0 + sum (0-1))  => sum 0 == 0           -- for: assert (sum 0 == 0)


        (sum 0 == if 0 <= 0 then 0 else 0 + sum (0-1))  
     && (sum 1 == if 1 <= 0 then 0 else 1 + sum (1-1))  => sum 1 == 1           -- for: assert (sum 1 == 1) 

     
        (sum 0 == if 0 <= 0 then 0 else 0 + sum (0-1))  
     && (sum 1 == if 1 <= 0 then 0 else 1 + sum (1-1))  
     && (sum 2 == if 2 <= 0 then 0 else 2 + sum (2-1))  => sum 2 == 3           -- for: assert (sum 2 == 3) 
    

        (sum 0 == if 0 <= 0 then 0 else 0 + sum (0-1))  
     && (sum 1 == if 1 <= 0 then 0 else 1 + sum (1-1))  
     && (sum 2 == if 2 <= 0 then 0 else 2 + sum (2-1))  
     && (sum 3 == if 3 <= 0 then 0 else 3 + sum (2-1))  => sum 2 == 3           -- for: assert (sum 3 == 6) 
     

Sure, now we can verify things about `sum` but its silly
- which "inputs" should we "call" `sum` with? 


Programs as Proofs
==================

Lets write some "operators" that make it possible to write "proofs as programs".

The "Equation" Combinator
=========================

```
(===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y}
x === y = y 
```

**Precondition**  : Input arguments must be equal
**Postcondition** : Output value equals inputs

Combinator Structures Programs as Equational Proofs
=========================

Lets write a "proof" that `sum 2 == 3`

\begin{code}
{-@ sum_2_equals_3 :: _ -> { sum 2 == 3 } @-} 
sum_2_equals_3 _  = () 
\end{code}

Now another proof that `sum 3 == 6`

\begin{code}
{-@ sum_3_equals_6 :: _ -> { sum 3 == 6 } @-} 
sum_3_equals_6 _  = () 
\end{code}

The "Because" Combinator
====================

The `?` lets you "add" some "known fact" into a proof 

```
(?) :: a -> b -> a 
x ? coz = x 
```

That the output is just the input `x` ... 

... but *refined* with the extra *knowledge* that is in `coz`

Because You Shouldn't Repeat Yourself 
=====================================

Lets rewrite the proof of `sum 3 == 6` but *reusing* the proof of `sum 2 == 3`

\begin{code}
{-@ sum_3_equals_6' :: _ -> { sum 3 == 6 } @-} 
sum_3_equals_6' _  
  =   sum 3 
  === 3 + sum 2
      ? sum_2_equals_3 ()
  === 6
\end{code}


A Real Proof 
============

Lets try to *specify* and *prove* that:

    for all natural numbers n:  0 + 1 + ... + n == (n * (n - 1) / 2)

First, lets "prove" it "by hand"

    ...

Next, lets 

1. *Specify* this fact as a *type* ?

    ...

2. *Verify*  this fact as a *term* ? 
    
    ...