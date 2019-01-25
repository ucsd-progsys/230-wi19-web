
\begin{code}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--short-names" @-}
module ReasoningAboutFunctions where 

import Prelude hiding (sum)
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
assert :: Bool -> a -> a
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
     
     
(sum 2 == if 2 <= 0 then 0 else 2 + sum (2-1))  => sum 2 == 2 + sum 1

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
sum_3_equals_6' :: () ->Int
sum_3_equals_6' () 
  =   sum 3 
  === 3 + sum 2
      ? sum_2_equals_3 ()
  === 6
\end{code}

A Proper Proof  
==============

Lets try to *specify* and *prove* MJ's property:

    for all natural numbers n:  n <= sum n 

Another Real Proof 
==================

Lets try to *specify* and *prove* that:

    for all natural numbers n:  2 * sum n == n * (n - 1)

First, lets "prove" it "by hand"

    -- TODO IN CLASS 

Next, lets 

1. *Specify* this fact as a *type* ?

    -- TODO IN CLASS 

2. *Verify*  this fact as a *term* ? 
    
    -- TODO IN CLASS 

Peano Numbers
=============

\begin{code}
data Peano = Z | S Peano 
  deriving (Eq, Show)
\end{code}

Elements of the type are

\begin{code}
p0, p1, p2, p3 :: Peano
p0 =         Z      -- zero
p1 =       S Z      -- one 
p2 =    S (S Z)     -- two
p3 = S (S (S Z))    -- three
\end{code}

Adding Peanos
=============

Lets write a function that `add`s two `Peano` numbers 

\begin{code}
-- >>> add Z (S (S Z)) 
-- S (S Z)

-- >>> add (S Z) (S (S Z)) 
-- S (S (S Z))

-- >>> add (S (S Z)) (S (S Z)) 
-- S (S (S (S Z)))

{-@ reflect add @-}
add         :: Peano -> Peano -> Peano 
add Z     m = m 
add (S n) m = S (add n m)
\end{code}

Adding Zero 
===========

Lets specify and verify that

    forall p. add Z p == p 

-- DO IN CLASS


Next, lets specify and verify that

    forall p. add p Z == p 

-- DO IN CLASS

Addition is Commutative 
=======================

-- HEREHERE REVISIT theorem_MJ 

Finally, lets specify and verify that

    forall p1 p2. add p1 p2 == add p2 p1

-- DO IN CLASS

Lists 
===

Recall the definition of lists

\begin{code}
data List a = Nil | Cons a (List a)
  deriving (Eq, Show)
\end{code}

Appending Lists
===

Lets write a function to `app`end two lists

\begin{code}
{-@ reflect app @-}
app :: List a -> List a -> List a 
app Nil ys         = ys 
app (Cons x xs) ys = Cons x (app xs ys)
\end{code}

Lists are like Peanos 
===

For example, appending a Nil returns the original list 

Lets specify and verify that

    forall l. app Nil l == l 

-- DO IN CLASS


Next, lets specify and verify that

    forall l. app l Nil == l 

-- DO IN CLASS


Lists are Ordered Data 
===

So we can, e.g. fiddle around with the order. 

Lets write a function to `rev`erse a list, so 

\begin{code}
-- >>> rev (Cons 0 (Cons 1 (Cons 2 (Cons 3 Nil))))
-- Cons 3 (Cons 2 (Cons 1 (Cons 0 Nil)))
rev :: List a -> List a 
rev = undefined 
\end{code}


Btw, lets do a sanity check: if we `rev` a list twice, 
we should get back the original:

\begin{code}
-- >>> rev (Cons 0 (Cons 1 (Cons 2 Nil)))
-- Cons 2 (Cons 1 (Cons 0 Nil))

-- >>> rev (Cons 2 (Cons 1 (Cons 0 Nil)))
-- Cons 0 (Cons 1 (Cons 2 Nil))

-- >>> rev (rev (Cons 0 (Cons 1 (Cons 2 Nil))))
-- Cons 0 (Cons 1 (Cons 2 Nil)))
\end{code}

Sure, but does that hold *for all lists* ? Can we prove

    forall l. rev (rev l) == l

Lets first try to prove "by hand"...

-- DO IN CLASS

... oops, need to know what happens if you 

    app (rev xs) (rev ys) 

-- DO IN CLASS

... oops, need to know what happens if you 

    app (app xs ys) zs 

-- DO IN CLASS

We can use these *helper functions* (aka *lemmas*) to go 
and finish off our theorem about `rev (rev xs)`.



Trees 
=====


Here's a `Tree` data type

\begin{code}
data Tree a = Tip | Node (Tree a) a (Tree a)
  deriving (Show)
\end{code}

Some example trees 

\begin{code}
{-@ reflect tt @-}
{-@ reflect t1 @-}
{-@ reflect t2 @-}
{-@ reflect t3 @-}
tt, t1, t2, t3 :: Tree Int
tt = Tip 
t1 = Node tt 1 tt 
t2 = Node tt 3 tt 
t3 = Node t1 2 t2 
\end{code}


Reversing a Tree 
===

What's the equivalent of `rev` on a `Tree` ?

\begin{code}
-- >>> revTree (Node (Node Tip 1 Tip) 2 (Node Tip 3 Tip))
--     Node (Node Tip 3 Tip) 2 (Node Tip 2 Tip)
revTree :: Tree a -> Tree a 
revTree = undefined

{-@ reflect mirror @-}
mirror :: Tree a -> Tree a 
mirror Tip          = Tip 
mirror (Node l a r) = Node (mirror r) a (mirror l)


\end{code}

Reversing twice 
===
    
Lets prove that 

    forall t. revTree (revTree t) == t 

-- DO IN CLASS