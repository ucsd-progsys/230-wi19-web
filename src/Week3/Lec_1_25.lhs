Friday Jan. 25

Recall Peano: we had the add function (see notes in Lec_1_18.lhs)

\begin{code}
{-@ reflect add @-}
add :: Peano -> Peano -> Peano  
add Z     m = m 
add (S n) m = S (add n m)
\end{code}

We proved if you add 2 and 2 you get 4 and if you add Z and p you get p. 
But what if we want to prove that add p Z = p?

**Proof techniques:

First write down the goal: You want <some statement> === <some other statement>.
Then instead of === put ==!and try to get rid of the ! in steps.

Let's prove add is commutative: x+y = y+x
Formally, forall x y,  add x y === add y x
First the base case: prove that add 0 y == add y 0
But we're using Peano, so we're really proving add Z y == add y Z.
Here's our first try:

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
    ==! add y (S x')
\end{code}

That won't work because it's a circular proof. We need an extra theorem
that says S (add y x') === add y (S x'). Here's how we start:

\begin{code}
{-@ lemma :: y:_ -> x':_ ->{ S (add y x') == add y (S x')} @-}
lemma :: Peano -> Peano -> Proof
lemma :: undefined --tbd later
\end{code}

We can rename some variables so that this is more general. Next, we probably want
 to split on a because that's the variable that's recursed on in add. We also 
 switched the left and right sides of the statement in the refinement.

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

Now, with the lemma, we can prove commutativity. Here's the final proof.

\begin{code}
{-@ thm_add_comm :: x:_ -> y:_ -> {add x y == add y x} @-}
thm_add_comm :: Peano -> Peano -> Proof
thm_add_comm Z y 
    = add Z y
    === y
        ? thm_Z_add y
    *** QED

thm_add_comm (S x') y
    = add (S x') y
    === S (add x' y)
        ? thm_add_comm x' y
    === S (add y x')
        ? lemma y x'
    === add y (S x')
    *** QED
\end{code}

Note: When we prove a statement is true because of some reason using "?", the ? 
proves that the line above it is equal to the line below it.

Instead of writing lemma, we COULD have changed the definition of add. But other
 things would have broken.

Now another proof, looking at lists. The append function for two lists is as follows:
\begin{code}
data List a = Nil | Cons a (List a)
    deriving (Eq, Show)

{-@ reflect  app @-}
app :: List a -> List a -> List a
app Nil ys          = ys
app (Cons x xs) ys  = Cons x (app xs ys)

\end{code}

We're proving app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) == Cons 1 ( Cons 2 ( Cons 3 Nil))).
Start by figuring out what we're splitting on (well, that's easy, it's l - the only
 thing we CAN split on).

\begin{code}
{-@ ex_list :: () -> {app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) == Cons 1 ( Cons 2 ( Cons 3 Nil)))} @-}
ex_list :: () -> Proof
ex_list _ 
    = app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) 
    === Cons 1 (app Nil ((Cons 2 (Cons 3 Nil))))
    === Cons 1 (Cons 2 (Cons 3 Nil))
    *** QED

{-@ thm_app_nil :: l:_ -> {app l Nil == l} @-}
thm_app_nil Nil 
    = app Nil Nil
    === Nil
    *** QED

thm_app_nil (Cons h t) 
    = undefined

\end{code}

Now we'll flesh out the recursive case. What are we trying to prove?

\begin{code}
thm_app_nil (Cons h t) 
    = app (Cons h t) Nil -- This doesn't work yet.
    === Cons h t -- The solver doesn't know the line above implies this line.
    *** QED

\end{code}

And now that we know that, how are we going to get there? We need to show that app t Nil
 = t.

\begin{code}
thm_app_nil (Cons h t) 
    = app (Cons h t) Nil
    === Cons h (app t Nil)
        ? thm_app_nil t
    === Cons h t
    *** QED
\end{code}

Final theorem: associativity. In addition, that means x + (y + z) = (x + y) + z
We'll split on the first argument again: it can be either Nil or a list.

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
