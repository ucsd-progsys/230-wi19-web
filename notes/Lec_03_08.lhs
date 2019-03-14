
FHTriple
{P} c {Q}

P = Precondition
Q = Postcondition
c = Command

===================================================================
Rules to figure out if FHTriple holds

-------------------------------------------
-- Skip 
------------------------------------------- 

If we have c = Skip and some precondition P
Q - What possible postcondition is legit??
A - P

Therefore {P} Skip {P}, which gives us our skip rule.

------------------------[Skip]
{P} Skip {P}

for all s, s' 
IF bval P s && BStep Skip s s'
THEN bval P s'
becuase s = s'

\begin{code}
--------------------------------------------------------------------------------
-- | The type `Assertion` formalizes the type for the 
--   assertions (i.e. pre- and post-conditions) `P`, `Q`
--   appearing in the triples {P} c {Q}

type Assertion = BExp 

--------------------------------------------------------------------------------
-- | Proof of the Skip rule 
--------------------------------------------------------------------------------
{-@ lem_skip :: p:_ -> (Legit p Skip p) @-}
lem_skip :: Assertion -> Legit 
lem_skip p = \s s' (BSkip {}) -> () 
\end{code}

Q - what is that backslash in the lem_skip code?
A - We have to return a 'Legit' which is a function. Hence, we use \ to say that we are returning a function 
    which takes two state, a BStep and returns a proof. Everythng after backslash before -> are arguments to the function.
  
-------------------------------------------
-- Assignments 
------------------------------------------- 

{P} x := 10 {x >= 0}
Q - What is P for which this is always true??? 
A - Any precondition aka TRUE

{P} x := y {x >= 0}
Q - What is P for which this is always true??? 
A - y >= 0

{P} x := 10 {x + y >= 0} 
P = 10 + y >= 0

Note that here there are lot of values of y which are okay. 
Weakest requirement is y >= -10. 

{P} x := A + B {x + y >= 10}
P = A + B + y >= 10

{P} x:= a {Q}
Q - What should P be for this triple to be legit??
A - Q with x replaced with a i.e Q[x|-a]

E.g.
      IF
      Q - x >= 100
      c - x = x + 1
      THEN
      P - (x + 1 >= 100) (i.e. x |- x + 1)

Hence, we get this rule: 

----------------------------[Assignment]
 {Q[x|-a]} x := a {Q}

\begin{code}
-- This lemma proves the 'legit' ness of the Assignment rule described above

{-@ lem_asgn :: x:_ -> a:_ -> q:_ -> (Legit (bsubst x a q) (Assign x a) q) @-}
lem_asgn :: Vname -> AExp -> Assertion -> Legit
lem_asgn x a q = \s s' (BAssign {}) -> lem_bsubst x a q s
\end{code}

-------------------------------------------
-- Sequences 
------------------------------------------- 

For, {P} c1;c2 {Q} to be Legit something must be true in middle after c1 and before c2

Let's take an example:

{?} x := 10; y := 10 {x = y}

Q - What should be a valid precondition here?
A - TRUE (i.e. any state)

{TRUE} x := 10; y := 10 {x = y} is a legit triple.

Q - But why is this triple legit ?
A - 

-----------------------[Assignment]   ----------------------[Assignment]
{10=10} x := 10 {x = 10}             { x = 10} y := 10 {x = y}
-----------------------------------------------------------------------
{10=10} x := 10; y := 10 {x = y}

Here 10 = 10 is same as TRUE

An another example: 

{10 > 1 } x := 10 { x > 1}        { x > 1} y := 1 { x > y }
--------------------------------------------------------------
{10 > 1 } x := 10; y := 1 {x > y}


Hence, we get our sequence rule:

{P} c1 {MID}     {MID} c2 {Q}
-----------------------------[Seq rule]
{P} c1;c2 {Q}

Q - Would these proofs work with FALSE instead of TRUE??

-----------------------         ---------------------------
{FALSE} x := 10 { x = 10 }        { x = 10 } y := 10 {x = y}
--------------------------------------------------------------
{FALSE} x := 10; y := 10 {x = y}

Here in the Triple {FALSE} x := 10 {x = 10}, we can't go from postcondition x = 10 
to FALSE becuase we don't have a rule for doing that. If we use assignment rule on this triple,
it says that P can be 10=10 and nothing else. So even though it would be a legit triple with {FASLE} we don't have rules to deduce that.


{x=4} y := x {y > 0} -- This is a legit triple
BUT, there are no rules till now which lets us prove this
The only thing we can prove with assignment rule is that

{x > 0} y:= x {y > 0}
which is not the same as 
{x=4} y := x {y > 0}

We need more rules as we can't prove some legit triples to be legit

-------------------------------------------
-- Consequence 
------------------------------------------- 

{x > 0} y:= x {y > 0} is fine becuase we used proven assignment rule

Q - How {x > 0} y:= x {y > 0} relates to {x=4} y := x {y > 0} ???
A - (x = 4) implies (x > 0)

We can think of this relation in terms of a cloud of states

 _____________
/             \      execute c        ___________
\    /\       / ------------------>   |         |
 \   \/P'    /                        |         |
  \_________/P                        |_________|Q

If you start out in any state s in which P is true and after executing command c you land in any state s' where Q is true
then if you start from any subset of P (P' in the figure), command c would still take you to a state where Q is true
With reference to our example,  P is all states where   x > 0
                                P' is all states where  x = 4


Implication

    p1 => p2 (implication)
    for any s, if p1 evals to true in s then p2 eval to true in s

So, x=4 implies x > 0
means
In any state s in which x = 4 is true
    x >0 is also true

\begin{code}
-- type to formalize implication
type Implies P1 Q = s:_ -> {bval P1 s} -> {bval P s}
\end{code}

Hence, we get our two Consequence rules: 

{P} c {Q}    P1 => P
-----------------------[Consequence Pre rule]
{P1} c {Q}

{P} c {Q}    Q => Q1
-----------------------[Consequence Post rule]
{P} c {Q1}