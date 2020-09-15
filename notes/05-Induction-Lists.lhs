
\begin{code}
module Induction where 
\end{code}

Friday Jan. 25

In the previous lecture, we solved some very basic theorems like sum of  first n natural numbers with 
mathematical induction using ProofCombinators. We also introduced Peano numbers and the add operation 
on them. (See notes in Lec_1_18.lhs)

\begin{code}
{-@ reflect add @-}
add :: Peano -> Peano -> Peano  
add Z     m = m 
add (S n) m = S (add n m)
\end{code}

We proved that if you add 2 and 2 you get 4 and if you add Z and p you get p. But what if we want to 
prove that add p Z = p? In other words, we want to prove the additive identity property that says: 
    add p Z = add Z p = p.

**Proof techniques:
1. First write down the goal: You want <some statement> === <some other statement> as the post-condition 
    of the theorem. In this case, we want to prove: add p Z = p.
2. Then we define the base case for p = Z, proving which is trivial.
3. Next, we define the theorem for any p, and we use recursive call of the same theorem on the 
    predecessor of p. This tells liquid to assume that the theorem is true for smaller inputs, which 
    lets us use the equality in the post condition - just like mathematical induction. And since we are 
    calling the same theorem on a smaller input, it also satisfies the termination checker.


\begin{code}
{-@ thm_Z_add :: p:Peano -> { add p Z == p } @-} 
thm_Z_add :: Peano -> Proof 
thm_Z_add Z                     -- base case
    = add Z Z 
    === Z 
    *** QED 

thm_Z_add (S p)                 -- induction step
    = add (S p) Z 
    === S (add p Z) ? thm_Z_add p 
    === S p 
    *** QED 
\end{code}

**Tip:
With === operator, liquid verifies that the arguments are in fact logically equivalent. While debugging, 
we can use ==! operator to tell liquid to trust on the equivalence and skip the check. So we can start with 
==! operator and try to get rid of it in steps. 

Next, let's prove that the add operation is commutative: x+y = y+x
Formally, forall x y,  add x y = add y x
Following the previous example, lets start with the base case: add Z y == add y Z.

Here's our first try:

\begin{code}
{-@ thm_add_comm :: x:_ -> y:_ -> {add x y == add y x} @-}
thm_add_comm :: Peano -> Peano -> Proof

thm_add_comm Z y 
    = add Z y
    === y
        ? thm_Z_add y
\end{code}

Note that we made use of additive identity property we proved above. Next, we move on to the general case 
where we unfold the definition and recursively apply the theorem again.

\begin{code}
thm_add_comm (S x') y
    = add (S x') y
    === S (add x' y)
        ? thm_add_comm x' y
    === S (add y x')
    ==! add y (S x')
\end{code}

We are not done yet because liquid still doesn't know how to verify that last step. Here, we need an extra 
theorem that says S (add y x') === add y (S x'). So lets declare the lemma first and see how it looks.

\begin{code}
{-@ lemma :: y:_ -> x':_ ->{ S (add y x') == add y (S x')} @-}
lemma :: Peano -> Peano -> Proof
lemma :: undefined --tbd later
\end{code}

We can rename some variables so that this is more general. Next, we probably want to split on the input "a" because 
that's the variable that's recursed on in add. We also switched the left and right sides of the statement in the refinement.

\begin{code}
{-@ lemma :: a:_ -> b:_ ->{ add a (S b) == S (add a b)} @-}
lemma :: Peano -> Peano -> Proof
lemma Z b  -- Note that this b is not the same as the following b's 
    = add Z (S b) -- This b is the Peano preceeding the b above
    === S b -- this is true because of thm_Z_add
    === S (add Z b) -- true because of the definition of add, case add Z _
    ***QED
lemma (S a') b
    = add (S a') (S b) 
    === S (add a' (S b))    -- definition of add
        ? lemma a' b        
    === S (S (add a' b))    -- true because of the lemma
    === S (add (S a') b)    -- definition of add
    ***QED
\end{code}

Now, with the lemma, we can go back to proving commutativity. Here's the final proof.

\begin{code}
{-@ thm_add_comm :: x:_ -> y:_ -> {add x y == add y x} @-}
thm_add_comm :: Peano -> Peano -> Proof

thm_add_comm Z y 
    = add Z y
    === y
        ? thm_Z_add y

thm_add_comm (S x') y
    = add (S x') y
    === S (add x' y)
        ? thm_add_comm x' y
    === S (add y x')
        ? lemma y x'
    === add y (S x')
\end{code}

**Questions:
1. How does liquid go about evaluating ?
    When we prove a statement is true because of some reason using ?, the ? operator proves that the line above 
    it is equal to the line below it.

2. Could we have changed the definition of add instead of writing the lemma? 
    Yes, we COULD have changed the definition of add. But we might end up changing it's functionality 
    that might break the code elsewhere.

3. How do we know what paramters to plug into the theorem while calling itself?
    Based on pattern matching. Haskell pattern-matches function calls to its definitions to fish out parameters 
    supplied to the definitions.

Now another proof, looking at lists. The append function for two lists is defined as follows:

\begin{code}
data List a = Nil | Cons a (List a)
    deriving (Eq, Show)

{-@ reflect  app @-}
app :: List a -> List a -> List a
app Nil ys          = ys
app (Cons x xs) ys  = Cons x (app xs ys)
\end{code}

Say we want to prove a simple case that's true by definition: 
    app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) == Cons 1 ( Cons 2 ( Cons 3 Nil))).
Start by figuring out what we're splitting on (well, that's easy, it's l - the only thing we CAN split on).

\begin{code}
{-@ ex_list :: () -> {app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) == Cons 1 ( Cons 2 ( Cons 3 Nil)))} @-}
ex_list :: () -> Proof
ex_list _ 
    = app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) 
    === Cons 1 (app Nil ((Cons 2 (Cons 3 Nil))))
    === Cons 1 (Cons 2 (Cons 3 Nil))
    *** QED
\end{code}

And next, on to proving the identity property of list append operation - similar to add of Peano numbers.
Again, we start with the base case.
\begin{code}
{-@ thm_app_nil :: l:_ -> {app l Nil == l} @-}
thm_app_nil Nil 
    = app Nil Nil
    === Nil
    *** QED

thm_app_nil (Cons h t) 
    = undefined
\end{code}

Now we'll flesh out the recursive case. Lets first note down what we are trying to prove.

\begin{code}
thm_app_nil (Cons h t) 
    = app (Cons h t) Nil -- This doesn't work yet.
    === Cons h t -- The solver doesn't know the line above implies this line.
    *** QED

\end{code}

Liquid does not know how to prove that equality by itself. So we unfold the definition of "app" and use the theorem
recursively on smaller list. So here's how the final definition looks.

\begin{code}
thm_app_nil (Cons h t) 
    = app (Cons h t) Nil
    === Cons h (app t Nil)
        ? thm_app_nil t
    === Cons h t
    *** QED
\end{code}

To wrap up, lets prove one final property of list append operation: associativity. To define it formally:
    forall lists a, b, c, app (app a b) = (app a b) c
We repeat the same steps as we did for all the theorems above: unfold the definitions and use the theorem recursively.
Here's the final theorem:

\begin{code}
{-@ thm_app_assoc :: l1:_ -> l2:_ -> l3:_ -> {app (app l1 l2) l3 == app l1 (app l2 l3) } @-}
thm_app_assoc :: List a -> List a -> List a -> Proof
thm_app_assoc Nil ys yz
    = app (app Nil ys) zs
    === app ys zs -- true because of the definition of app Nil anything
    === app Nil (app ys zs) -- true because of the definition of app Nil anything
    *** QED

thm_app_assoc (Cons x xs) ys zs 
    = app (app (Cons x xs) ys) zs
    === app (Cons x (app xs ys)) zs -- true because of the definition of app (Cons x xs) ys
    === Cons x (app (app xs ys) zs) -- same as above line
        ? thm_app_assoc xs ys zs -- this line is the reason the line below is true
    === Cons x (app xs (app ys zs))
    === app (Cons x xs) (app ys zs) -- true because of app: this line is the left of the recursive case of app, the line above is the right
    *** QED
\end{code}
