Week 2 - Fri - 18 Jan 2019
==========================

#### Recap: 
* Last time we were looking at the 'sum' function, and we saw how we can use the 'equation combinator' operator to prove statements by unfolding the definition of the 'sum' function.
* We also saw the 'because combinator' operator, which allows you to reuse facts that you have already used before.

We stopped last class at **proving something for all n**. The example statement we were using was 'for all n, n <= sum n'.

Recall the 'sum' function:

\begin{code}
module ProofCombinators where

import Prelude hiding (sum)
{-@ reflect sum @-}                                 
sum :: Int -> Int 
sum n = if n <= 0 
    then  0                   -- "base"      case 
    else  n + sum (n-1)       -- "recursive" case
\end{code}

We started a theorem for this assertion as:

\begin{code}
{-@ theorem_MJ :: n:Int -> { n <= sum n} @-}
theorem_MJ :: Int -> Proof 
theorem_MJ 0 = undefined
\end{code}

Is there an easy way to prove this - without changing the post-conditions/specifications of anything, or even without changing code anywhere?

* One suggestion: to change the post-condition on 'sum' so that it always returns a Nat
    * This by itself doesn't work (though it would be enough if the assertion was sum n >= 0)
* Another suggestion: to add another step to the above which uses the (===) operator. Specifically,
    * sum n === n + sum (n-1)
    * The solver can now infer that sum (n-1) >= 0 from the post-condition. 
    * This works.

* A simpler solution is to just change the post-condition on sum to say it returns something >= n
    * That is, {-@ sum :: n : Int -> {v : Nat | n <= v} @-}

* How about if we don't want to change the type of 'sum' at all? That is, we want to spell out theorem_MJ explicitly.
    * For this, we can do a case split: whether n <= 0, or otherwise.
    * This looks like the following (we leave the Nat return type in the refinement type for 'sum'):

\begin{code}
{-@ theorem_MJ :: n : Int -> {n <= sum n} @-}
theorem_MJ :: Int -> Proof
theorem_MJ n
        | n <= 0    = ()
        | otherwise = sum n
                  === n + sum (n-1)
                  =>= n
                  *** QED
\end{code}

This is our first interaction with the (=>=) operator. The definition of this operator is as follows (note that it is rather like the (===) operator, but for >= rather than ==):
\begin{code}
{-@ (=>=) :: x:a -> y:{a| x>= y} -> {v:a | v == y} @-}
x =>= y = y
\end{code}

This is also our first look at the *** QED syntax. The expression "x *** QED" is a **proof certificate** that is strong enough for the SMT solver to prove your theorem.
The relevant code snippet from ProofCombinators.hs is

\begin{code}
infixl 3 ***
{-@ assume (***) :: a -> p:QED -> { if (isAdmit p) then false else true } @-}
(***) :: a -> QED -> Proof
_ *** _ = ()

data QED = Admit | QED

{-@ measure isAdmit :: QED -> Bool @-}
{-@ Admit :: {v:QED | isAdmit v } @-}
\end{code}

Notice that the *** operator returns a unit () type. 
This is the reason we have to return () for the n <= 0 case - so that the different cases have matching return types.

In all the proofs we deal with, we usually never care about the 'value' of the proof. This is why we just return a unit () type.

However, this still results in an error! 
* One possible fix was to add some further info about (n-1)?
* Another suggestion was that there are some glitches happening due to the associativity properties of the (=>=) operator.  
We are leaving this as an exercise to find out why there is an error here, and to remove it.

Let us now look at another property of the 'sum' function, namely that sum n = n*(n+1)/2
To avoid division, we move the 2 to the left hand side of the equation we try to prove.

The mathematical formulation of our statement then is:
\forall n >=0, 2 * sum n = n * (n+1)

How would we prove this by hand? 
* We would use induction on n
    * Base case:            n = 0. Here, we just put 0 in place of n in the equation. Clearly it holds.
    * Inductive hypothesis: 
        * Here we assume the equation holds for all n = 0, 1, ..., (k-1). Then, we want to prove that it also holds for n = k
        * For n = k:
            2 * sum k = 2 * (k + sum (k-1))
                      = 2 * k + 2 * sum (k-1)
                      = 2 * k + (k-1) * k       -- since we know from the inductive hypothesis that 2 * sum(k-1) = (k-1)* k
                      = k^2 + k
                      = k * (k+1)

We want to turn this proof into a program.
* Remember that all our theorem statements become types - this means we need to turn our theorem statement into a type signature.
* We then want to implement some code that has this type signature. If we can do that, then the implementation of that is a proof of this theorem!
* Also, note that the type 'Proof' is just another name for the unit () type.

The completed theorem looks as follows:
* Note that we have two cases for the implementation, corresponding to the base case and inductive hypothesis.

\begin{code}
{-@ thm_sum :: n:Nat -> { 2 * sum n == n * (n + 1) } @-}
thm_sum :: Int -> Proof 
thm_sum 0 
    = 2 * sum 0 
  === 0 * (0 + 1) 
  *** QED 

thm_sum k 
    = 2 * sum k
  === 2 * (k + (sum (k-1))) 
  === 2 * k + 2 * (sum (k-1))
      ? thm_sum (k-1)
  === k * (k + 1)
  *** QED 
\end{code}

The (==!) operator is an uncheck operator - it does not actually check if the mentioned equation holds. 
* This is useful in proof debugging, as you can use it to stop error messages at times. 
* But it is not safe to use this in an actual proof - so it can never be in your final solution.

An important concept is the recursive call to "thm_sum (k-1)" - this is the inductive hypothesis!
* We do this by using the 'because operator' (?)

This recursive call raises the question, can we just say "thm_sum k = thm_sum k *** QED"?
* This is not legitimate. But why would Liquid Haskell complain?
    * It will not terminate! It is necessary for a proof to terminate.
    * A recursive call must always be with a smaller input.
    * Therefore our theorem above works because the recursive call is to (k-1).

Question: Does it matter where you call the (?) operator? 
Answer: 
* It does matter. (?) is a local check. 
* It won't work if we give the fact later, because the error will come up when Liquid Haskell tries to check an equality that doesn't hold without the fact.
* Liquid Haskell won't pull information from the 'future'.

Some takeaways:
* The statement of the theorem corresponds to the type definition of the function.
* Case splitting is like branching in a program. (you can write the proof as an if-then-else program too)
* Induction corresponds to writing a recursive function.

Now, we move to proofs on types that are not integers. 

### Peano Number
This is an encoding of numbers:
* zero = Z
* one  = S Z
* two  = S (S Z)
* and so on...

S means 'successor'

Peano numbers can also be thought in terms of a List data structure, albeit one with no data inside the elements. 
* In this analogy, Z would correspond to Nil, S would corresond to something else (say More).

\begin{code}
data Peano 
  = Z 
  | S Peano 
  deriving (Eq, Show)
\end{code}

You can implement arithmetic on this encoding of numbers. We want to write a function that adds two Peano numbers.

\begin{code}
{-@ reflect add @-}
add :: Peano -> Peano -> Peano  
add Z     m = m 
add (S n) m = S (add n m)
\end{code}

Now that we have this add function, we can prove some theorems that use add.

\begin{code}
{-@ thm_2_add_2_eq_4  :: _ -> { add (S (S Z)) (S (S Z)) == S (S (S (S Z))) }  @-}
thm_2_add_2_eq_4 :: () -> Proof 
thm_2_add_2_eq_4 _ 
  =   add (S (S Z)) (S (S Z)) 
  === S (add (S Z) (S (S Z)))
  === S (S (add Z (S (S Z))))
  === S (S ((S (S Z))))
  === S (S (S (S Z)))
  *** QED 
\end{code}

This is just straightforward unfolding of the add function definition. 

Another theorem: we want to prove that for all p, add Z p == p 
\begin{code}
{-@ thm_add_Z :: p:Peano -> { add Z p == p } @-} 
thm_add_Z :: Peano -> Proof 
thm_add_Z p = add Z p === p *** QED 
\end{code}

Symmetrically, what about if we flip the order of the arguments? This becomes a bit more complicated.
* To do this, we would have to do some induction.
    * There will be a base case (when the input is Z), that is "add Z Z"
    * There will be an inductive case (when the input is some (S p)), that is, "add (S p) Z"

\begin{code}
{-@ thm_Z_add :: p:Peano -> { add p Z == p } @-} 
thm_Z_add :: Peano -> Proof 
thm_Z_add Z     
    = add Z Z 
    === Z 
    *** QED 

thm_Z_add (S p) 
    = add (S p) Z 
    === S (add p Z) ? thm_Z_add p 
    === S p 
    *** QED 
\end{code}

Notice in the second case the use of a recursive call as a fact. This works with the termination checker since "p" is smaller than "(S p)"

As an exercise, try out other examples:
* Check that the add operation is commutative (hint: do induction on the first argument.)
