### CSE 230: Programming Languages
### Winter 2019
### Instructor: Ranjit Jhala
### Scribe: Chen Fang & Yiwei Zhang
---------------
Below are the four cases of "Legit":

1.Legit {TRUE} c {Q} 
    This is not legit because {P=True} does not neccessarily impliy {Q=True};
2.Legit {False} c {Q}
    This it legit because false implies everything;
3.Legit {P} c {True}
    This is legit because {Q=True} no matter what P and c are;
4. Legit {P} c {False}
    This is not legit because {Q=False} no matter what P and c are;

Suppose we have the following legit statement:
    {P} c {Q}
then the question is: under what circumstances do we have:
    {P} c {Q'}

First, let's try:
    {Q' is a subset of Q}.
Example,
    Q  = {x >= 0}
    Q' = {x = 1}
where {x = 1} is a subset of {x >= 0}. Then we have:

        {True} c {x >= 0}
    ----------------------------
        {True} c {x = 1}

which is not true because {x >= 0} does not imply {x = 1}.

Let's try the other way around, which states:
    {Q' is superset of Q}
Example:
    Q' = {x >= 0}
    Q  = {x =  1}
where {x >= 1} is a subset of {x = 0}. Then we have:

        {True} c {x = 1}
    ----------------------------
        {True} c {x >= 0}

This is legit because {x = 1} implies (x >= 0), which leads us to the following conclusion:

    For any s, s', given 1) precondition P(s), 2) BStep c that steps from s to s',
    3) postcondition Q(s'), then the following is legit:

        {P} c {Q}
    ---------------------
        {P} c {Q'}
    
    if Q implies Q', or Q is a subset of Q'.


Let's look at another case:
        {P} c {Q}
    -----------------------
        {P'} c {Q}

With the same analysis,  we say that the above statement is legit if
    P' implies P (represented as P' => P), or P' is subset of P.

Example:
        {x >= 0} c Q
    --------------------------
        {x = 5} c Q

This is legit because {x = 5} => {x >= 0}.

In summary, we can fuse the above two rule into one, shown as follows:

        P => P'     {P'} c {Q'}     Q' => Q
    ----------------------------------------------
                    {P} c {Q}


If we specify {c = Skip}:

    {False} Skip {False} -- legit
    {False} Skip {True}  -- legit
    {True}  Skip {False} -- Not legit
    {True}  Skip {True}  -- legit

The statements can be represented as the truth table, with 1 being True and 0 being False:
    0 0 1
    0 1 1
    1 0 0
    1 1 1
This corresponds to the boolean implication operation: P => Q. It can be further generalized to:

    If P, Q such that 
        {P} Skip {Q}
    is legit, then it must be
        {P => Q}.

Next We will derive some rules using:
    - Consequence Rule
    - Skip Rule

Recall the "Consequence Rule":

P => P'     {P'} c {Q'}     Q' => Q
---------------------------------------
            {P} c {Q}

With:
    P = False
    P'= True
    Q = True
    Q' = True

We have:    

False => True   {True} Skip {True}      True => True
----------------------------------------------------- 
            {False} Skip {True}

We can use a 'mid' condition to expand our proof tree. In this case, it is {x==10}. 

First, x:=10 implies {x==10} so we can get: {True} x:=10 {x==10} on the left hand side. 
Then we use the implication rule {True => 10==10}: {10==10} x:=10 {x==10}.
Similarly on the right hand side, we first use the assignment rule to get the proof {y==10}
because {y==10 => y>=0} we can write the proof as {x==10} y:=x {y>=0}.

                      -------------------- Asgn             --------------------- Asgn
  {True => 10==10} {10==10} x:=10 {x==10}                     {x==10} y:=x {y=10}   {y=10 => y>=0}
------------------------------------------                  -----------------------------------------
        {True} x:=10 {x==10}                                        {x==10} y:= x {y>=0}
------------------------------------------------------------------------------------------------------------
                                 {True} x := 10; y := x {y >= 0}

With the same 'mid' condition approach, we can change our method a little bit. We can first prove {x>=0} and
then use the assignment rule to get the final proof {y>=0}

--------------------------------------- Asgn
    True => 10==10 {10>=0} x:=10 {x>=0}       
--------------------------------------- Consequence                   ------------------------ Asgn
        {True} x := 10 {x>=0}                                         {x>=0} y:= x {y >= 0}
------------------------------------------------------------------------------------------------------------
                                   {True} x := 10; y := x {y >= 0}


The 'IF' proof tree should mean the following: given a command 'IF b THEN c1 ELSE c2' and the precondition 'P',
the postcondition 'Q' is always True. Intuitively, we might simply write the proof tree as follows:

{P} c1 {Q}        {P} c2 {Q}    
-----------------------------
    {P} IF b c1 c2 {Q}

However, this condition is too strong in that it says either c1 or c2 under the precondition 'P' can lead to 'Q'.
Consider a simple counterexample: {True} IF x>=0 THEN y:=x ELSE y:=0-x {y>=0}. It essentially means the absolute
value of any x must be no less than 0, which should undoubtedly hold. If we adopt the above proof tree, it would
be as follows:

{True} y:=x {y>=0}          {True} y:=0-x {y>=0}
-------------------------------------------------
  {True} IF x>=0 THEN y:=x ELSE y:=0-x {y>=0}

It doesn't make sense since the tree is correct only when x is equal to 0. In addition, it doesn't work on the BExp 'b'. 
If we think more carefully, we can see that if b is evaluated to be True, the precondition would become {P and b}, 
otherwise it would become {P and (not b)}.

{P and b} c1 {Q}        {P and (not b)} c2 {Q} 
-----------------------------------------------
           {P} IF b c1 c2 {Q}

Then the above example would look like:

{x>=0} y:=x {y>=0}          {not (x>=0)} y:=0-x {y>=0}
--------------------------------------------------------
      {True} IF x>=0 THEN y:=x ELSE y:=0-x {y>=0}

Now it holds for any number x.