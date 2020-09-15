### CSE 230: Programming Languages
### Winter 2019
### Wednesday, January 30 (Lecture 9)
##### Instructor: Ranjit Jhala
##### Scribe: Michael Borkowski

#### Wrapping up [Monday's lecture:](Lec_01_28.lhs)

We left off last time with the proof of thm_rev_app undefined. This theorem 
states that the reverse of two lists appended together is the reverse of the 
second followed by the reverse of the first. For example,

\begin{code}
    rev ([a1, a2, a3] `app` [b1, b2, b3])
=== rev [a1, a3, a3, b1, b2, b3]
=== [b3, b2, b1, a3, a2, a1]
=== [b3, b2, b1] `app` [a3, a2, a1]
=== (rev [b1, b2, b3]) `app` (rev [a1, a2, a3])
\end{code}

Recall that we needed this theorem as a step in our proof that the reverse of
the reverse of a list is always equal to the list itself.

We have everything we need to work out the proof of thm_rev_app now. The base case 
is relatively straightforward. We use the definition of app to drop a Nil in the
first argument. We then append a Nil to the end of (rev bs) which requires citing 
a lemma from last Friday's lecture. thm_app_nil states:
    forall xs. app as Nil == as
Here's the theorem statement and the base case:

\begin{code}
{-@ thm_rev_app :: as:_ -> bs:_ -> { rev (app as bs) == app (rev bs) (rev as) } @-}
thm_rev_app :: List a -> List a -> Proof 
thm_rev_app Nil bs 
    = rev (app Nil bs)                             -- fold def'n of app  
  === rev bs                                        ? thm_app_nil (rev bs)
  === (rev bs) `app` Nil                          *** QED --because Nil == rev Nil
\end{code}  

In the inductive case, we start out with rev (app (Cons a as) bs). Our goal is to 
somehow use the inductive hypothesis in a chain of `===` equality statements that 
the SMT solver can verify:

\begin{code}
thm_rev_app (Cons a as) bs 
    = rev (app (Cons a as) bs)			 
   -- ...
  ==! app (rev bs) (rev (Cons a as))              *** Admit 
\end{code}

We start by 
unfolding the definition of app and rev in order to obtain
    rev (app as bs) `app` (Cons a Nil)
Now we're getting somewhere, because the left hand side of the inductive hypothesis
appears as an arguemnt to `app`. Applying hypothesis we get:
    (rev bs `app` rev as) `app` (Cons a Nil)
That's not quite what we need yet; we need to get the `a` cons-ed back on to the 
head of the `as`. Recall from [last Friday's lecture](Lec_1_25.lhs) that `app`
is in fact associative:
    forall xs, ys, zs : List a. (xs `app` ys) `app` zs == xs `app` (ys `app` zs)
We use this along with the definition of `rev` to finish. Here's the complete proof 
of the inductive case:

\begin{code}
thm_rev_app (Cons a as) bs 
    = rev (app (Cons a as) bs)			   -- unfold def'n of app 
  === rev (Cons a (app as bs))                     -- unfold def'n of rev
  === rev (app as bs) `app` (Cons a Nil)            ? thm_rev_app as bs
  === (rev bs `app` rev as) `app` (Cons a Nil)      ? thm_app_assoc (rev bs) (rev as) (Cons a Nil)
  === (rev bs) `app` (rev as `app` (Cons a Nil))   -- fold def'n of rev
  === app (rev bs) (rev (Cons a as))              *** QED 
\end{code}

### Proofs about Programs: Arithmetic Expressions

Now we'll leave behind our Lists and our Peano numbers and turn to some more 
interesting objects, namely (simple fragments of) programming languages. This is a
shift in our focus:

Proofs (consisting) of Programs ==> Proofs about Programs

Last time we introduced a simple language of arithmetic expressions. These expressions
are addition (over \mathbb{Z}) of constants and variables. We define these expressions
recursively in (Liquid) Haskell:

\begin{code}
type Val   = Int
type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 
  deriving (Show)
\end{code}

This definition gives us expressions, not as flat strings, but as a recursively-defined
tree structure (i.e. an abstract syntax tree). 

At least for now, we'll fix the variable names to be Strings, the values to be integers
only, and restrict ourselves to only the addition operation.

We also have lookup tables that define an environment in which all of our variable
names are bound to values:

\begin{code}
type State = S.GState Vname Val
\end{code}

These states are just lists of variable names along with their values (and an extra
default value for undefined names).

Our states have `set` and `get` functions where we can bind values to variable names
as well as lookup the assigned value. Note that we have pure functions in Haskell, not 
object methods, so these operations are not "in-place"; they return a new State object.

For example, mentally simplifying our notion of State to just a list of (key,value) 
pairs then we could write the following (ignoring the notational complications 
introduced by the GState record type -- don't try typechecking this at home):

\begin{code}
s = [("x", 10), ("y", 20) ]
s'= S.set s "x" 105
assert (s' == [("x", 105), ("y", 20)] )
\end{code} 

We also wrote a function `aval` to evaluate an arithmetic expression with respect to a 
specific state. There are three cases: for a number (N k) we just return the value k, 
for a variable (V x) we lookup x in the state, and for a (Plus a1 a2) operation we 
recursively evaluate a1 and a2 and then add the results together. Observe that
this corresponds to a straightforward post-order traversal of the abstract syntax tree.

\begin{code}
{-@ reflect aval @-}
aval :: AExp -> State -> Val
aval (N k)        _ = k
aval (V x)        s = S.get s x
aval (Plus a1 a2) s = (aval a1 s) + (aval a2 s)
\end{code}

Let's illustrate evaluation with an example. We evaluate `ex2` below with respect to
the state `state1` which is S.init 10; an empty state with the default value of 10.
This amounts to replacing "x" and "y" with the default 10; adding it all up, we find
that ex2 evaluates to 24 as required in the postcondition.

\begin{code}
{-@ example :: { v: Int | v == 24 } @-} 
example :: Int
example = aval ex2 state1
  where 
    -- 12 
    ex0 = N 12 
    -- x + 9
    ex1 = (V "x") `Plus` (N 9)
    -- x + y + z
    ex2 = (V "x") `Plus` (V "y") `Plus` (N 4)
    
{-@ reflect state1 @-}
state1 :: State 
state1 = S.init 10 
\end{code}

#### Simplification

Next we'll look at some things we can do to simplify our expressions, as well as
what we can prove about the correctness of these simplifications. The first kind
of simplification that we'll look at is called _constant folding_: we want to
simplify an arithmetic expression by combining constants being added together

at the same level
We'll recursively traverse our AExp expression when simplifying

So we'll want to be able to perform the following simplifications:
         [YES] 4 + 9          ===>     13
         [YES] x + (4 + 9)    ===>     x + 13
         [YES] 2 + (4 + 9)    ===>     15 

We'll limit how much simplification that we'll try to do; for instance we won't use
the associativity of addition to fold together constants being added at different
levels. We could also add support for replacing additions with a 0 argument by just 
the other argument, but we leave that out for now for simplicity.
         [NO]  (x + 4) + 9    =/=>     x + 13
         [LATER]  x + 0       =/=>     x 

EXERCISE. Suppose we've augmented our arithmetic expressions with multiplication.
That is, we could rewrite our definition of an expression to include a constructor, say,
Mult AExp AExp. Then observe that these expressions can be thought of as polynomials
over the set of variables that appear in the expression. We could represent such a
polynomial, say, by a list of coefficients along with the corresponding term.
First, write a function that transforms an expression into a corresponding polynomial
type as well as a function to evaluate these polynomials with respect to a given state. 
Second, prove correctness under evaluation of these representations. In other words,
prove that for every state, the evaluation of the original expression is the same as
the evaluation of the corresponding polynomial.

Let's write the code for the constant folding function now, which we'll call 
`asimp_const`. If we have just a constant or a variable, we won't make any changes.
However if we have an expression of the form `Plus a1 a2` then there's some 
simplification that we may be able to do; If both a1 and a2 recursively simplify to
just a number, then we can replace those two numbers with their sum.
Note the use of the Haskell case construct; we first recursively simplify both a1
and a2. We then do a pattern matching against the form of 
(asimp_const a1, asimp_const a2) _not_ against (a1, a2) in order to identify the 
cases where we can indeed fold constants together.

\begin{code}
{-@ reflect asimp_const @-}
asimp_const :: AExp -> AExp 
asimp_const (N n) = N n
asimp_const (V x) = V x  
asimp_const (Plus a1 a2) = case (asimp_const a1, asimp_const a2) of 
  (N n1, N n2) -> N (n1 + n2) 
  (b1  , b2)   -> Plus b1 b2
\end{code}

What does it mean for `asimp_const` above to be correct? How do we know that we didn't
make any mistakes? In other words, we want to specify what it means for the input and
the output expressions of `asimp_const` to be "morally equivalent." The correct notion
of equivlance of two expressions is that for every possible state s, the two 
expressions evaluate to exactly the same answer with respect to this state. Evaluation
is given by the `aval` function so we can rephrase this as the condition:
    forall s:State. aval a1 s === aval a2 s

Then we can express the correctness of `asimp_const` as the equivalence of the input
and output expressions. We're quantifying over all expressions as well as all states, 
so the correctness becomes a two argument function AExp -> State -> Proof:
    foo :: a:AExp -> s:State -> { aval a s == aval (asimp_const a) s}

Now, there's another way that we could do this more precisely or systematically. We 
could first give a general type definition that captures the notion of equivalence of 
expressions, namely:
\begin{code}
   {-@ type Equiv A1 A2 = s:State -> { aval A1 s == aval A2 s } @-}
\end{code}
In other words the type Equiv is parameterized by two expressions. 

Let's carefully note that A1 and A2 are *not* type variables; they are actually values
that parameterize the Equiv type. We write `A1` instead of `a1` because by rule in
Liquid Haskell, the type parameters must be capitalized. An object of type Equiv A1 A2 
is then essentially just the same as a proof of the  postcondition that A1 and A2 
evaluate the same in every state.

Now that we have our type-def, we can then state our correctness theorem quite concisely
as:
\begin{code}
    {- lem_aval_asimp_const_ok :: a:_ -> Equiv a (asimp_const a) @-} 
\end{code}
The type-def style doesn't really give us anything we couldn't already express
perfectly well before, so we'll just prove the first form "foo" above.

Proof strategy: The structure of the function(s) that appear in the statement of the
theorem or lemma determine the structure of the proof. In this case, the relevant 
structure is that of `asimp_const` which breaks down the AExp argument by pattern
matching: a number (N n), a name (V x), and an addition (Plus a1 a2) which we further
break down into cases based on the recursive simplification of the sub-expressions
a1 and a2. So we can start by copying the branching structure of `asimp_const` into
our function definition `foo`, making sure to add the additional state argument.

The first two cases below are trivial. No constant folding is possible, so both sides
of the theorem reduce to `aval (N n) s` in the first case. We can just assign the 
proof to be () because the SMT solver can verify it without further help (if PLE is on).

In the third case (Plus a1 a2) we have to use the same `case (asimp_const a1,
asimp_const a2) of` cosntruct so that when we use the inductive hypothesis, we can use 
information about asimp_const of a1 and a2.

\begin{code}
{-@ foo :: a:_ -> s:_ -> { v:_| aval a s == aval (asimp_const a) s } @-}
foo :: AExp -> State -> Proof 
foo (N n)        _ = ()
foo (V x)        _ = () 
foo (Plus a1 a2) s = case (asimp_const a1, asimp_const a2) of 
    (N n1, N n2) ->  aval (Plus a1 a2) s                     -- def'n of aval
                 === (aval a1 s) + (aval a2 s)                ? foo a1 s ? foo a2 s
                 === (aval (N n1) s) + (aval (N n2) s)       -- def'n of aval
                 === n1 + n2                                 -- def'n of aval
                 === aval (N (n1 + n2)) s                    -- def'n of asimp_const
                 === aval (asimp_const (Plus a1 a2)) s      *** QED
    (b1  , b2)   ->  aval (Plus a1 a2) s                     -- def'n of aval
                 === (aval a1 s) + (aval a2 s)                ? foo a1 s ? foo a2 s
                 === (aval b1 s) + (aval b2 s)               -- def'n of aval
                 === aval (Plus b1 b2) s                     -- def'n of asimp_const
                 === aval (asimp_const (Plus a1 a2)) s      *** QED
\end{code}
  
We can simplify this proof a lot, and leave out a lot of the symbol pushing if we have 
"--ple" mode on. We replace our chain of equivalence with just the unit value () and 
the appropriate "because" combinator calls to our inductive hypothesis.

\begin{code}
{-@ foo2 :: a:_ -> s:_ -> { v:_ | aval a s == aval (asimp_const a) s } @-}
foo2 :: AExp -> State -> Proof 
foo2 (N n)        _ = ()
foo2 (V x)        _ = () 
foo2 (Plus a1 a2) s = case (asimp_const a1, asimp_const a2) of 
    (N n1, N n2) ->  () 
                      ? foo a1 s 
                      ? foo a2 s

    (b1  , b2)   -> () 
                      ? foo a1 s 
                      ? foo a2 s
\end{code}

Let's move on to a slightly better simplifier. Instead of a constant folding function,
we'll do our simplifications locally as an expression is built. Towards this end, we
introduce the idea of a "smart constructor," which is a function that builds values of
the correct type but adds some kind of functionality. In our case, this funcitonality 
is simplification on the fly. So we'll bake our constant folding (and even implement 
simplification of "x + 0" => "x") into the smart constructor `plus` which will take
the place of plain old Plus.

\begin{code}
{-@ reflect plus @-}
plus :: AExp -> AExp -> AExp 
plus (N i1) (N i2) = N (i1+i2) 
plus (N 0)  a      = a 
plus a      (N 0)  = a 
plus a1     a2     = Plus a1 a2
\end{code}

Note that the Haskell type signature of plus is the same as the type of Plus, so smart
plus functions the same way as Plus. How do we show that `plus` is a valid replacement
for Plus? This amounts to showing that (plus a1 a2) and (Plus a1 a2) are equivalent
expressions, in the sense that they evaluate to the same value in every state. We 
state this as a lemma. The proof is trivial in that no induction or lemmas are
required, so we assign every case as (). We still need to branch into cases according 
to the structure of a1 and a2 because Liquid Haskell needs to know about the structure
of a1 and a2 in order to unfold the definitions of `plus` and `aval`.

\begin{code}
{-@ lemma_aval_plus :: a1:_ -> a2:_ -> s:_ -> 
         { v:_ | aval (plus a1 a2) s = aval (Plus a1 a2) s } @-}
lemma_aval_plus :: AExp -> AExp -> State -> Proof 
lemma_aval_plus (N _) (N _) _ = () 
lemma_aval_plus (N 0) a     _ = () 
lemma_aval_plus a     (N 0) _ = () 
lemma_aval_plus a1    a2    _ = () 
\end{code}

Even if we don't make use of the smart constructor in building our expressions, we can
still use it to simplify the definition of asimp_const while still adding functionality
like ignoring "+ 0" terms. We get something cleaner and free of all the case splitting:

\begin{code}
{-@ reflect asimp @-}
asimp :: AExp -> AExp 
asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)
asimp a            = a 
\end{code}

As before, we have a correctness theorem for `asimp`. By calling the correctness lemma
for the constructor `plus` we've avoided the nasty nested case split. We may not have
seen the `&&&` combinator before. Essentially, it just combines proof certificates
together. It's more appropriate here than a sequence of "because" combinators because
we're not spelling out the steps.

\begin{code}
{-@ lemma_aval_asimp :: a:_ -> s:_ -> { v:_|aval (asimp a) s = aval a s } @-}
lemma_aval_asimp :: AExp -> State -> Proof 
lemma_aval_asimp (Plus a1 a2) s  =     lemma_aval_asimp a1 s 
                                   &&& lemma_aval_asimp a2 s 
                                   &&& lemma_aval_plus (asimp a1) (asimp a2) s
lemma_aval_asimp _ _             = () 
\end{code}

#### A Digression on Assignment 

So far we have talked about states as being these static, unchanging objects that exist
and to which we refer as needed to look up values. This has made sense thus far because 
our arithmetic expressions have no way at all to affect the state.

Now let's consider the idea of _assignment_ in a programmning language. Suppose we include
an assignment statement as part of our arithmetic expressions. Now evaluating expressions
can have an affect on the state. To be more precise, let's fix some notation. Let s refer 
to the starting state and write an assignment as 
    
    x := a

which will be understood as "take the expression a, evaluate it in state s, and use the
resulting value to update x". Call the resulting state s'. Note that a can be an 
arbitrary arithmetic expression, not just a constant value. So the assignment itself
depends on the state at the time.

We can illustrate this with the diagram below, where the downwards arrow represents the 
flow of time (or the flow of execution inside a larger program).

 |
 |   s 
 |       x := a 
 |   s' 
 |
\|/
 V (flow of time/execution)

Here's a concrete example:
 
 |   s = [("x",5),("y",10)]         -- our initial state
 |
 |       x := x + y                 -- x+y evaluates to 15 in s
 |
 |   s' = [("x",15),("y",10)]       -- so we update x to be 15
 |
\|/
 V (flow of time/execution)

We let our start state s = [("x", 5), ("y", 10)] and assign x+y to x. This evaluates
to 15, so we complete the assignment by updating x to 15.

Now suppose we have something other expression `e` and we want to know what is the 
value of `e` in state `s'`. How can we express the value of `e` in terms of `s` and 
`x := a`; that is, without explicitly referring to `s'`?

For example, suppose `e` is the boolean expression `x > 1000`. The value of `x > 1000`
in state `s'` is determined precisely by the assignment `x := a` and whether `a` is
in fact greater than 1000 or not (with respect to the previous state). So we can say
    x > 1000 (in state s')   if and only if   a > 1000 (in state s) 

 |
 |   s                         [a > 1000] here
 |
 |       x := a                 if and only if
 | 
\|/  s'                        [x > 1000] here
 V

This suggests a general answer: the value of expression `e` in state `s'` is equal to
the evaluation in `s` of the expression obtained by replacing every occurrence of `x` 
in `e` with `a`.

The "substitute `x` with `e` in `a`" part can be thought of as a substitution operation.
We'll define a function for it, which takes a variable name `x`, an expression `a` 
(being assigned to `x`), an expression `e` and returns another expression:

\begin{code}
-- substitute "x" with "a" inside "e"
subst :: Vname -> AExp -> AExp -> AExp 
subst x a (Plus e1 e2)   = Plus (subst x a e1) (subst x a e2) 
subst x a (V y) | x == y = a
subst _ _ e              = e 
\end{code}

Then we can express our answer above about the value of `e` in `s'` more precisely as:
  
    aval e s' == aval (subst x a e) s

Finally, let's state a correctness result: s' above is given by updating x to the 
evaluation of a, namely S.set s x (aval a s). We now have two ways to express the value
of `e` in `s'` which must be equal for `subst` to be correct: we can either update the
state `s` with the assignment and then evaluate e in the new state, *or* we can 
substitute `x` for `a` inside `e` and evaluate in the old state. This is expressed by
the `lem_subst`. The proof is left as an exercise (in the homework). 

\begin{code}
{- lem_subst :: x:_ -> a:_ -> e:_ -> s:_ 
          -> { aval e (set x (aval a s)) s  == aval (subst x a e) s @-}
\end{code}

#### Where do we go from here?

The next task will be to build a compiler for these arithmetic expressions. We will 
define a (very) small instruction set for an abstract stack machine, and then we'll
compile our expressions into this bytecode.

