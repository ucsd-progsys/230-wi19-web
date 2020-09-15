### CSE 230: Programming Languages
### Winter 2019
### Wednesday, February 6 (Lecture 12)
##### Instructor: Ranjit Jhala
##### Scribe: Jiaxiao Zhou

Last time, we discussed what it means to be even. 
We started with a familiar definition of Peano number datatype.

\begin{code}
data Peano where
    Z :: Peano
    S :: Peano -> Peano
\end{code}

In order to define evenness, the first way we can try is to define a function that checks 
whether or not a given number is even number. We can call this function `isEven`.

\begin{code}
isEven Z = True
isEven (S n) = not (isEven n)
\end{code}

The above code says that 
    zero is even. 
    forall number n, if n is even, then (S n) is not even. 

Similarly, we can have another definition of isEven which captures basically the same idea of evenness. 
It says that
    zero is even.
    one is no even.
    forall number n, if n is even, then (S (S n)) is even.

\begin{code}
isEven Z = True
isEven (S Z) = False
isEven (S (S n)) = isEven n
\end{code}

Besides functions and datatypes, another definition facility to define evenness is called Inductive Definitions.
Here is a inductive definition using generalized abstract datatypes:

\begin{code}
data EvP where
    Ev :: Peano -> EvP

data Ev where
    EvZ :: Ev
    EvS :: Peano -> Ev -> Ev

{-@ data Ev where
        EvZ :: Prop (Ev Z)
      | EvS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))
 @-}
\end{code}

It says that we defined two `rules` for Ev. 
The first rule is that zero is even.
The second rul is that if n is even, (S S n) is even.

This is the same idea as we see in the function definition of evenness.


We can visualize these two rules in a proof tree as showed following:

To prove two is a even number. 

----------- EvZ
    Ev 0

    Ev n
----------- EvS
 Ev(S(S n))


To prove four is a even number.

    Ev 0
----------- EvZ
    Ev Z
----------- EvS
 Ev (S (S Z))
----------- EvS
Ev (S S S S Z)


The nature question is why is this even inductive definition correct?

When we are really certain about two definitions of the same thing, we want to prove that these two definitions are the same thing.
For example, we want to prove that inductive definition of even numbers agrees with the function definition of even numbers. 
To formalize this idea, we want to prove the following two things:

-- n:_ -> isEven n -> Prop (Ev n)
-- n:_ -> Prop (Ev n) -> isEven n

If we can do both things, although we don't know what even means, we do know that isEven and Ev n mean the same thing. 
That's we creat a one-to-one correspondence between these two different definitions. 

Now, let's focus on proving the following theorem first:

\begin{code}
{-@ lem_isEven :: n:_ -> Prop (Ev n) -> { isEven n } @-}
lem_isEven :: Peano -> Ev -> Proof
lem_isEven Z pf = ()
lem_isEven (S Z) pf = impossible ""
\end{code}

First of all, we want to split cases on Peano. 
The easy case is that when n is Z, we are done since plt will automatically unfold the definitions for us.
Next, we will just enumerate Peano to try other cases. We can show this lemma is True for input number one (S Z). 
In fact, as we all know, (S Z) should not be an even number. Then we are running into an issue that we don't know what to do next.

We can split cases on the proof. This is called Induction on the structure of derivation.

\begin{code}
{-@ lem_isEven :: n:_ -> Prop (Ev n) -> { isEven n } @-}
lem_isEven :: Peano -> Ev -> Proof
lem_isEven Z pf            = ()
lem_isEven (S Z) EvZ       = ()
lem_isEven (S Z) (EvS _ _) = ()
lem_isEven n pf            = undefined
\end{code} 

Both cases are contradictions since they never happen. The system knows this is a contradiction so that we can put () at the end. 

Now we are done for numbers 0 and 1. 0 is an even number and 1 is not. Next, we want to prove for more general number m.

\begin{code}
{-@ lem_isEven :: n:_ -> Prop (Ev n) -> { isEven n } @-}
lem_isEven :: Peano -> Ev -> Proof
lem_isEven Z pf            = ()
lem_isEven (S Z) EvZ       = ()
lem_isEven (S Z) (EvS _ _) = ()
lem_isEven (S (S m)) (EvZ) = ()
lem_isEven (S (S m)) (EvS _m ev_m) = isEven (S (S m))
                                 === not (not (isEven m))
                                 === isEven m
                                   ? lem_isEven m ev_m
                                 === True
                                 *** QED
\end{code} 

How can we prove the last case? the second argument is a proof of what the first argument is. EvS is a proof that (S (S m)) is even. 

"call" lem_isEven on m ev_m ===> gives a proof that "isEven m". Our goal is to prove "isEven (S (S m))". So we unfold the definition of isEven,
and then apply the recursive call if lem_isEven. Note that the proof is long, but we can use ple solver to reduce it. 

Now let's do the opposite direction. We want to prove that given a number n, if we know isEven n returns True, we want to show that Ev n is satisfied.

\begin{code}
{-@ lemon :: n:_ -> { isEven n } -> Prop (Ev n) @-}
lemon :: Peano -> Proof -> Ev
lemon n pf = undefined
\end{code}

This proof carries the fact that isEven of n. We can simplify the above code to:

\begin{code}
{-@ lemon :: n:{Peano | isEven n}-> Prop (Ev n) @-}
lemon :: Peano -> Ev
lemon n = undefined
\end{code}

We don't want to prove this forall n's. There is only one thing we can split cases on, which is Peano. 

\begin{code}
{-@ lemon :: n:{ v:Peano | isEven v}-> Prop (Ev n) @-}
lemon :: Peano -> Ev
lemon Z         = EvZ
lemon (S Z)     = impossible "never happen"
lemon (S (S m)) = EvS m (lemon m)
\end{code}

Again, we don't need to prove the second case becuase it is impossible. If we know `m` is even, then we know (S (S m)) is even. 
To construct that `m` is even, we need to use succesor rule, which takes a number and a proof. Hence it should take `m` as the number, and a proof that `m` is even which can be done by recursively call lemon on n.


Question: Why do we go from (S Z) to S (S m) instead of (S m)?

\begin{code}
{-@ lemon :: n:{ v:Peano | isEven v}-> Prop (Ev n) @-}
lemon :: Peano -> Ev
lemon Z         = EvZ
lemon (S Z)     = impossible "never happen"
lemon (S m)     = case m of
                    Z -> impossible "are you clever?"
                    S mm -> Evs mm (lemon mm)
\end{code}

The reason that the case (S (S m)) is easier is: if we want to use induction hypothesis, we want to work with an even number. We dont know whether or not
(S m) is even or not. If we know (S m) is even, then m is not even. But this does not help us that much. With (S (S m)), if we know m is even, we know (S (S m)) is even. 

We know that (S m) is even, so m is old. we can case split m:
If m is Z      --> impossible because this is exactly the second case
If m is (S mm) --> this case reduces to the case when we have (S (S m)).

Now we are done with even number.
------------------------------------------------------------------------------------------------------------

Definition: a relation between some sets A and B is just a subset of product of the sets A x B.
For example, we can define a relation on set Humans x Humans. Then all of the following examples are relations.

(Nalini, Nalini)
(Nalini, Ranjit)
(Alex, Nalini)

Another example is that we can define a relation on N x N, where N denotes the nature number set. 
We can define this relation to be that the second element of the pair is always bigger than the first element of the pair.
The following are valid relations.

(0,1)
(1,2)

Now let's formalize the idea of relation in code:

We can define relation as a boolean function, which takes two inputs and return a boolean. 
We can say either these two inputs are in relation or they are not in relation.

\begin{code}
type Rel a = a -> a -> Bool
\end{code}

After we defined a relation, we can define the Reflexive Transitive Closure.

The Reflexive Transitive closure, called * (star) below, is a function that maps a binary predicate to another binary predicate. 
What does it mean to be Reflexive? It means that x and x are in star relation for all x in R.
What does it mean to be Transitive? 
              If (x,y) in R, 
                 (y,z) in R^*, 
              then (x,z) in R^*.

We can express these two as rules to be visualized below:

--------At home
Star r x x 

How to think about Transitive?
Think about it as a directed graph
If there is a path from x -> y, and there is a path from y -> z, then there is a path from x -> z. 

    r x y AND Star r y z
--------------------------Step
        Star r x z

Now let's write them into the code:

\begin{code}
data StarP a where
    star :: Rel a -> a -> a -> StarP a

data Star a where
    Refl :: Rel a -> a -> Star a
    Step :: Rel a -> a -> a -> a -> Star a -> Star a

{-@ data Star a where
      Refl :: r:Rel a -> x:a -> Prop (Star r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Star r y z) -> Prop (Star r x z)
@-}
\end{code}


EXERCISE:
prove that lemmastar_trans:"star r x y -> star r y z -> star r x z"

we can use step rule
x -> x1 ---> y ---> z
     x1 ----------> z by induction