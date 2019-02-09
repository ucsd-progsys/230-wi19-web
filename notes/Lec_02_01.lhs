### CSE 230: Programming Languages
### Winter 2019
### Wednesday, Feb 01 (Lecture 10)
##### Instructor: Ranjit Jhala
##### Scribe: Chenwei Dai & Yue Zhao

#### Recap:
We have finished talking about regular induction. Last time we talked about Arithmetic 
Expressions and constant folding in expression simplification.

Suppose that we have a constant simplifier. If the two arguments are both numbers, we will have 
a number. But what if either is not a number? We do a case split here and both cases are needed for use of the 
simplifier constructor.

\begin{code}
{-@ reflect asimp_const @-}
asimp_const :: AExp -> AExp
asimp_const (N n) = N n
asimp_const (V x) = V x 
asimp_const (Plus a1 a2) = case (asimp_const a1, asimp_const a2) of
 (N n1, N n2) -> N (n1 + n2)
 (b1  , b2)   -> Plus b1 b2
\end{code}

Now we want to prove the equivalence of expressions. The equivalence means for any 
state s, the value of original expression is the same as the simplifier expression's value. 
We expect the proof looks like the function itself. Let’s split cases into three. In the first case, the input is a number N, and the 
output is also a number N. So `aval (asimp_const a) s` and `aval a s` are the same 
thing. And the variable is similar because that is what is happening in the definition itself. The most interesting case is Plus. 
Why could we just leave it as that? In a sense, we need to split cases to how actual function behaves. We will go through a simple example that makes kind of the same issue.

\begin{code}
{-@ lemma_aval_asimp_const :: a:_ -> s:_ -> { aval (asimp_const a) s = aval a s } @-}
lemma_aval_asimp_const :: AExp -> State -> Proof
lemma_aval_asimp_const (N _) _ = ()
lemma_aval_asimp_const (V _) _ = ()
lemma_aval_asimp_const (Plus a1 a2) s
    = case (asimp_const a1, asimp_const a2) of
        (N _, N _) -> lemma_aval_asimp_const a1 s &&& lemma_aval_asimp_const a2 s
        (_  , _)   -> lemma_aval_asimp_const a1 s &&& lemma_aval_asimp_const a2 s
\end{code}

Q: Why is the "case-of" important in the proof?
Let’s first suppose we have a silly function.

\begin{code}
{-@ reflect silly @-}
silly :: AExp -> Int 
silly (N _)        = 0
silly (V _)        = 0 
silly (Plus a1 a2) = silly a1 + silly a2 
\end{code}

And we want to prove therom `lem_silly` where `silly a == 0`. The reason I split it is we 
do not have enough information about what a is in order to make this step. When a is number, `silly a == 0` 
according to the definition. The second case is similar. And we use induction to prove 
the final case recursively.

\begin{code}
{-@ lem_silly :: a:_ -> { silly a == 0 } @-} 
lem_silly :: AExp -> Proof 
lem_silly (N _)      = () 
lem_silly (V _)      = () 
lem_silly (Plus a1 a2) = lem_silly a1 &&& lem_silly a2  
\end{code}

So, after the proof which has the same structure as the function we are trying to think about, 
we can talk about the proof that is same as the function we talked about. 

Now let's build a small stack machine:

### Stack Machine
An example:
For an expression ((x+2) + ((3+y)+10))
Traverse a tree using inorder to generate the result of the expression:
                        +
                    /        \
                   +           +   
                /    \       /   \
              x       2     +    10
                           /  \
                           3   y
  
Let's transform it to a normal form. Which means for every plus, the left-hand argument must be a variable.
So we write it in such a form: (x+y) + (2+3+10) = x+y+15.
The exercise is called full_simplify. You should write a function to do this transformation first.
Then you need to prove your simplifier is correct.
However, what we do now is a different exercise. We'll build a small stack machine, which takes an expression and compilers it down to a sequence of machine instructions. 
The instruction is defined as following:

\begin{code}
data Instr
 = LOADI Val
 | LOAD  Vname
 | ADD
 deriving (Show)

type Stack = [Val]
\end{code}

An example:
Here’s an toy example to illustrate how we compile this expression:
(2+4) + (7+x)
We want to transform the expression to a sequence of machine instructions. Here `LOADI` 
is for constant and `LOAD` is for variable. We need a stack to hold temporary values. 
Initially, my stack is empty. Stack after each instruction is in the comment. Let’s 
say `X = 100` here.
[
		        // []
LOADI 2,  	// 2:[]
LOADI 4,	  // 4:2:[]
ADD,		    // 6:[]
LOADI7,	    // 7:6:[]
LOAD “X”,	  // 100:7:6:[] 
ADD		      // 107:6:[]
ADD		      // 113:[]
]

So the program is a list of instructions and stack is a list of values. Now we write 
a function exec1. It takes the next instruction you want to run, state(there is only one state), current stack 
and give the output stack. 

\begin{code}
{-@ reflect exec1 @-}
exec1 :: Instr -> State -> Stack -> Stack
exec1 (LOADI n) _ stk       = n           : stk
exec1 (LOAD x)  s stk       = (S.get s x) : stk
exec1 ADD       _ (j:i:stk) = (i+j)       : stk
exec1 _         _ _         = []
\end{cdoe}

#### Q & A: why not write “impossible” here?
A: If we use “impossible”, we need to prove it is in fact impossible. Actually it is 
not impossible. In this case, we do not really care.

We define `exec` to process multiple instructions. The key idea is to execute next instruction and recursively excute the remaining instructions from that set.

\begin{code}
{-@ reflect exec @-}
exec :: [Instr] -> State -> Stack -> Stack
exec []     _ stk = stk
exec (i:is) s stk = exec is s (exec1 i s stk)
\end{code}

### Compiling Arithmetic Expressions to a Stack Machine
Now let’s write a function `comp`. It takes an expression, and give a sequence of instructions.
The difference is that it does not look at state or stack. We use `append` here.

\begin{code}
{-@ reflect comp @-}
comp :: AExp -> [Instr]
comp (N n)        = [LOADI n]
comp (V x)        = [LOAD x]
comp (Plus a1 a2) = comp a1 ++ (comp a2 ++ [ADD])
\end{code}

### Correctness of compilation

#### Q1: How can we DEFINE the correctness of compilation?
The result of execution of a series compiled instructions is the same as the value of 
that original expression.

#### Q2: How can we PROVE the correctness of compilation?
Here’s some thinking:
\begin{code}
{-@ thm_comp :: a:_ -> s:_ -> stk:_ -> { exec (comp a) s stk = cons (aval a s) stk } @-}
thm_comp :: AExp -> State -> Stack -> Proof
thm_comp (N n)        s stk = () -- exec [LOADI n] s stk === n : stk ***QED
thm_comp (V x)        s stk = () -- exec [LOAD x] s stk === (S.Get s x) : stk ***QED
thm_comp (Plus a1 a2) s stk 
= exec (comp (Plus a1 a2)) s stk
=== exec (comp a1 ++ comp a2 ++ [ADD]) s stk
-- === exec [ADD] s (exec (comp a2) s (exec (comp a1) s stk))
-- === exec [ADD] s (exec (comp a2) s (aval a1 s : stk))
== === exec [ADD] s (aval a2 s : aval a1 s : stk)
==! cons (aval (Plus a1 a2) s) stk  --need a lemma here
***QED
\end{code}

As we can see, to complete the proof, we need a lemma. This lemma tells us that, the 
result of our execution of instructions is equal to the result of dividing these 
instructions into two parts and then executing them in order.

The complete proof is as follows:
\begin{code}
{-@ reflect comp @-}
comp :: AExp -> [Instr]
comp (N n)        = [LOADI n]
comp (V x)        = [LOAD x]
comp (Plus a1 a2) = comp a1 ++ (comp a2 ++ [ADD])

{-@ thm_comp :: a:_ -> s:_ -> stk:_ -> { exec (comp a) s stk = cons (aval a s) stk } @-}
thm_comp :: AExp -> State -> Stack -> Proof
thm_comp (N n)        s stk = ()
thm_comp (V x)        s stk = ()
thm_comp (Plus a1 a2) s stk = lemma_exec_append (comp a1) (comp a2 ++ [ADD]) s stk
                           &&& lemma_exec_append (comp a2) [ADD] s stk1
                           &&& lemma_comp a1 s stk
                           &&& lemma_comp a2 s stk1
 where
   stk2                      = exec (comp a2) s stk1
   stk1                      = exec (comp a1) s stk

{-@ lemma_exec_append :: is1:_ -> is2:_ -> s:_ -> stk:_ ->
     { exec (is1 ++ is2) s stk = exec is2 s (exec is1 s stk) }
 @-}
lemma_exec_append :: [Instr] -> [Instr] -> State -> Stack -> Proof
lemma_exec_append []       _   _ _   = ()
lemma_exec_append (i1:is1) is2 s stk = lemma_exec_append is1 is2 s (exec1 i1 s stk)
\end{code}

