### CSE 230: Programming Languages
### Winter 2019
### Monday, February 4 (Lecture 11)
##### Instructor: Ranjit Jhala
##### Scribe: Michael Borkowski


#### Wrapping up [Friday's lecture:](Lec_02_01.lhs)

Last time we defined our compiler `comp` and the accompanying stack machine with a
minimal instruction set. We started to prove that the compiler is correct, but we 
needed a lemma. We were able to reason that in the case of a `Plus a1 a2` expression,

\begin{code}
        exec (comp (Plus a1 a2)) s stk
    === exec (comp a1 ++ (comp a2 ++ [ADD])) s stk
\end{code}

but we weren't able to unfold the execution of two sequence of Instrs appended together.

In general, what's the result of executing instruction sequences `is1` followed by 
`is2` in state `s` on stack `stk`? Executing the concatenated program `is1 ++ is2` must
be the same as running `is2` on the stack that results from running `is1` on `stack`. In
other words:

    forall is1, is2, s, stk. exec (is1 ++ is2) s stk == exec is2 s (exec is1 s stk)

We didn't get to prove this in class last time, so we prove this as a lemma today. As
usual, the forall over the two instruction sets, the state and stack become a multi-
argument function.

\begin{code}
{-@ lemma_instr_seq :: is1:_ -> is2:_ -> s:_ -> stk:_ -> 
           { v:_ | exec (is1 ++ is2) s stk == exec is2 s (exec is1 s stk) } @-}
lemma_instr_seq :: [Instr] -> [Instr] -> State -> Stack -> Proof
lemma_instr_seq []       is2 s stk   = () -- exec ([] ++ is2) s stk == exec is2 s stk
                                      -- === exec is2 s (exec [] s stk) *** QED
lemma_instr_seq (i1:is1) is2 s stk   = exec ((i1:is1) ++ is2) s stk
                                   === exec (i1:(is1 ++ is2)) s stk
                                   === exec (is1 ++ is2) s stk1
                                           ? lemma_exec_append is1 is2 s stk1
                                   === exec is2 s (exec is1 s stk1)
                                   === exec is2 s (exec (i1:is1) s stk) *** QED
  where
    stk1 = exec1 i1 s stk
\end{code}

We prove by induction on the first sequence of instructions. In the induction case,
we use the relationship between cons and append 
    ((i1:is1) ++ is2) == i1:(is1 ++ is2)
in order to "peel off" the first instruction so that we can apply the induction
hypothesis on running (is1 ++ is2) in state s with stack (exec1 i1 s stk).

Note that our use of the inductive hypothesis is valid even though the stack is in
some sense bigger: `exec1 i1 s stk` as opposed to the original `stk`. It's still valid
because we're doing induction on the size of the first instruction sequence; the 
induction hypothesis assumes that the lemma is proven for smaller `is1` and for *any*
stack `stk` (as well as any `is2` and `s`). So we only need to shrink the first argument.

The where construct allows us to assign local variables in order to make our proofs
more readable. We can then use this lemma to finish proving thm_comp (see the 
[notes from Friday](Lec_02_01.lhs).


### Induction on Evidence

Up to this point we have been doing induction on the objects that we wanted to 
prove properties about. We started with the natural numbers, proving statements
such as:

  forall n : Nat, 2 * sum n == n * (n+1)

and then we generalized this to structural induction over lists, and proved 
statements like

  forall xs : rev (rev xs) == xs

We assume the property holds for all tails and then proved for every head `cons` 
tails. We could also think of this as induction on the length of the list. Then
we moved to arithmetic expressions where now we had two base cases (for a numeric
value and for a variable) and one inductive case (Plus a1 a2).

However, in the PL field we also want to do proofs by induction "on the proof
itself". In other words, we want to be able to build proofs inductively and prove
theorems about the proofs themselves using induction. This means creating data 
structures to represent proofs, which we shall see shortly. For now, it will help 
to clarify things by looking an extended example.

#### A Concrete Example: Evenness and the Peanos

Recall our old friends, the Peano numbers:

  data Peano = Z | S Peano

We want to somehow define the notion of a number being even or not. We opened a
discussion on how do we define "even", and the following ideas were raised:

  1. We could define more general functions related to divisibility such as
     `divide-by-2` or `mod 2` and define an even predicate in terms of these.

  2. We could define evenness recursively on the Peano numbers with a function
     we'll call isEven. We could define it as follows:
\begin{code}
isEven :: Peano -> Bool
isEven Z     = True
isEven (S n) = not (isEven n)
\end{code}
  3. We could make a new type that captures the even Peano numbers, but this 
     ultimately wouldn't capture a subset of the Peano numbers being even.

One thing that all of these have in common is that we can say, for instance,
(isEven k) but that just states the fact that `k` is even and doesn't say why
or carry a proof that `k` is even.  Looking ahead to bigger things, we might
have a predicate `isWellTyped p` where `p` is a program. We won't just want to 
know that `p` is well-typed, but also _why_ `p` is well-typed and what inferences
were made in the process of the typecheck concluding this.

So sometimes we'll want a way to describe facts that contains both the fact being
described and information why it is true. Now we'll look at a way to define
evenness that encapsulates both of these.

We introduce a _proof system_ for evenness, in terms of a predicate `Ev`. For some
Peano number `p`, `Ev p` is the statement that p is even. Our proof system will
allow us to infer true statements. The rules in the proof system have the usual 
look from PL papers; that is, they have the form:

  IF <hypotheses>
  ---------------
  THEN <consequence>

with zero or more hypotheses on top, and a consequence on bottom. If we can infer all
of the hypotheses, then we can conclude the consequence below the line. A rule can 
have a blank top, which means the bottom is true unconditionally. These correspond 
to our base cases. Here are our rules:


  --------[EvZ]
    Ev Z

       Ev n
  --------------[EvS]
   Ev (S (S n))

The first rule says that Z (zero) is even, and is in and of itself a proof that Z is
even. The second rule says that if we know that `n` is even, then we can can conclude 
that `S (S n)` is also even. 

The rules can be combined to build up proofs of evenness in a "bottom-up" manner. It 
means that if we have a proof that `Ev n` is true, then the second rule [EvS] can be
added to this proof to yield a proof that `Ev (S (S n))` is true. In this manner we
can form a proof tree, say for showing that S (S (S (S Z))) is even (i.e. four):


      --------[EvZ]
        Ev Z
    --------------[EvS]
     Ev (S (S Z))
  ----------------------[EvS]
   Ev (S (S (S (S Z))))

We'd like to return not just a boolean when we ask about evenness but a representation
of this as some kind of type in our Liquid Haskell Program. The representation will be
a tree using plain data types, as we shall see shortly.

#### Digression: Haskell data types

So far we've been defining Haskell data types in the standard way, in terms of the
constructors (and any type variables):

 data List a = Nil | Cons a (List a)

We can also write this definition in an equivalent way in terms of constructor types:
\begin{code}
    data List a where 
        Nil  :: List a
        Cons :: a -> List a -> List a
\end{code}
Similary, instead of 

  data Peano = Z | S Peano

we can write
\begin{code}
data Peano where
  Z :: Peano
  S :: Peano -> Peano
\end{code}

Both of these forms are entirely equivalent, but we'll prefer the latter form, especially
for the ease it allows in writing refinement types.

#### Constructing Proofs of Evenness

First, we want to define a type that represent the statements we'll make about evenness.
\begin{code}
data EvP where
  Ev :: Peano -> EvP
\end{code}
In other words, the `Ev` constructor takes any Peano `n` and returns a proposition `Ev n` 
of type `EvP`. So far these are just statements.

Next, we define the type that is the proof tree of the evenness property. We define it in
terms of the two ways to construct the evidence.
\begin{code}
{-@ data Ev where
      EvZ :: Prop (Ev Z) 
    | EvS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n))) @-}

data Ev where
  EvZ :: Ev 
  EvS :: Peano -> Ev -> Ev 
\end{code}
The two constructors for type `Ev` correspond exactly to the two proof rules [EvZ] and
[EvS] that we gave above. `EvZ` takes no arguments and returns a tree node that is a 
proof that Z is Even. The rule `EvS` takes a Peano `n`, a proof of the evenness of `n` 
and returns a tree that is a proof of the evenness of `S (S n)`. So now our proof trees 
have a representation in Liquid Haskell as a tree-based data structure.

We won't go into the details of `Prop` used above in the refinement type, other than
that it is a parameterized type that represents proofs/evidence of specific statements
of type `EvP`.

Now, how can we generate a proof in Liquid Haskell that corresponds to the tree above
where we proved that "four" is even? We have to crawl before we can walk, so let's start
with zero and then prove "two" is even as a baby step.

The type of a proof that zero is Even must be Prop (Ev Z). How do we come up with a 
witness that zero is even? It's just the `EvZ` constructor.

\begin{code}
{-@ zero_is_Even :: Prop (Ev Z) @-}
zero_is_Even :: Ev 
zero_is_Even = EvZ 
\end{code}

Next, the type of a proof that two is even is `Prop (Ev (S (S Z)))` as we discussed
above. To come up with a proof witness, we'll want to use the `EvS` constructor along
with Z and a proof that zero is even:

\begin{code}
{-@ two_is_Even :: Prop (Ev (S (S Z))) @-}
two_is_Even :: Ev 
two_is_Even = EvS Z EvZ 
\end{code}

Now we're ready to write a proof that four is even. We use the `EvS` constructor again
along with the above proof `two_is_Even` to write:

\begin{code}
{-@ four_is_Even :: Prop (Ev (S (S (S (S Z))))) @-}
four_is_Even :: Ev 
four_is_Even = EvS (S (S Z)) two_is_Even 
\end{code}

We could also express the data structure witnessing the proof that four is even 
directly as:
    EvS (S (S Z)) (EvS Z EvZ)
which is essentially exactly the same as the proof tree we diagrammed out above.

There might be one question remaining in the back of your mind: have we really
defined evenness? How do we know that our proof system doesn't contain any mistakes?
We haven't actually done anything to connect our `Ev` datatype to any other definition
of evenness. All we've really said is that we can construct proofs that zero has some
property, and that if n has this property, then n+2 has it also. In other words, is 
there a way that we can prove that this new notion actually captures all of the even 
numbers and only them?

To state such a theorem, we need some "ground truth" notion of eveness to compare our 
proof system to. For that purpose we'll use the `isEven` function defined earlier, to 
say that we can construct a witness in Prop (Ev n) if and only if isEven n. An "if and
only if" theorem has two directions.

One direction of our theorem will state that for every Peano n that Liquid Haskell 
knows is even, we can construct a proof witness of type Prop (Ev n):
    n:Peano -> { isEven n } -> Prop (Ev n)
or more concisely
    {n:Peano | isEven n} -> Prop (Ev n)

In the other direction, we state that given a Peano n and a proof of type Prop (Ev n),
then we can prove (to the SMT solver) that `isEven n` is true:
    n:Peano -> Prop (Ev n) -> { isEven n } 

Next time, we'll work out how to formally state and prove these theorems.

