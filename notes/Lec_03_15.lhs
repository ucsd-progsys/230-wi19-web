### CSE 230: Programming Languages
### Winter 2019
### Wednesday, March 15
##### Instructor: Ranjit Jhala
##### Scribe: Yiming Zhang

We start by looking at the loop

\begin{verbatim}
y := x
while (x != 0):
    x = x - 1
    y = y - 1
\end{verbatim}

Question: What is the loop invariant for this loop?

    1. x  = y : 
       this is true in each iteration and also at the end of the loop

    2. What about x != 0 ?
       this is not true after the last iteration when x = 1

    3. What about x != -1?
       what if x = -1 at the start

What is loop invariant?
It must satisfiy several requirements:
    1. The loop invariant must be true at the start of the loop
    2. The loop invariant must be true in any iteration
    3. The loop invariant must be true after the loop

This is also illustrated by

                |
        (inv)   |<-------------------
                V                    |
               _____     T           |
        ______|  b  |________        |
       |      |_____|        |       |
    F  |                     V       |
       V                    _____    |
                           |  c  |---
                           |_____|  

where b is the loop condition, c is the loop body, and inv is loop invariant.

--note: it is hard to compute the exact loop invariant, and 70% of PL papers after
        about figuring out what the loop invariant is.

For each iteration: {inv && b} c {inv}
After the loop:     {inv && not b}

Now we look at the verification condition (vc).

Given preconditon p, some command c, and post condition q, we want to generate vc 
such that
\begin{verbatim}
    vc valid => legit p c q
\end{verbatim}

Reminder: pre c q is a precondition such that if execute command c, we end up with q true
i.e. by our construction, we have legit (pre c q) c q

Hence, all we need is that p => (pre c q), and we can use consequence to get legit p c q

We need to somehow check the validity of side conditions.
Now we can build a verifier :

\begin{verbatim}
    {-@ verify :: p:_ -> c:_ -> q:_ -> Valid (vc' p c q) -> () @-}
    verify :: Assertion -> ICom -> Assertion -> Valid -> () 
    verify _ _ _ _ = ()
\end{verbatim}

Consider each case:
1. for skip and assign, it is straightforward.

\begin{verbatim}
    {-@ lem_skip :: p:_ -> (Legit p Skip p) @-}
    lem_skip :: Assertion -> Legit 
    lem_skip p = \s s' (BSkip {}) -> () 

    {-@ lem_asgn :: x:_ -> a:_ -> q:_ -> 
        Legit (bsubst x a q) (Assign x a) q 
    @-}
    lem_asgn :: Vname -> AExp -> Assertion -> Legit 
    lem_asgn x a q = \s s' (BAssign {}) -> lem_bsubst x a q s
    \end{verbatim}

2. for seq, we need to check
        vc c1 (pre c2 q)
        vc c2 q

\begin{verbatim}
    {-@ lem_seq :: c1:_ -> c2:_ -> p:_ -> q:_ -> r:_ 
                -> Legit p c1 q -> Legit q c2 r 
                -> Legit p (Seq c1 c2) r 
    @-}
    lem_seq :: Com -> Com -> Assertion -> Assertion -> Assertion -> Legit -> Legit -> Legit 
    lem_seq c1 c2 p q r l1 l2 = \s s' (BSeq _ _ _ smid _ t1 t2) -> 
    l1 s smid t1 &&& l2 smid s' t2 
\end{verbatim}

3. for if, we compute side condition for c1 and c2. Both must be true so we use and

\begin{verbatim}
    {-@ lem_if :: b:_ -> c1:_ -> c2:_ -> p:_ -> q:_ 
            -> Legit (bAnd p b)       c1 q 
            -> Legit (bAnd p (Not b)) c2 q 
            -> Legit p (If b c1 c2)  q
    @-}
    lem_if :: BExp -> Com -> Com -> Assertion -> Assertion -> Legit -> Legit -> Legit
    lem_if b c1 c2 p q l1 l2 = \s s' bs -> case bs of 
    BIfF _ _ _ _ _ c2_s_s' -> l2 s s' c2_s_s'
    BIfT _ _ _ _ _ c1_s_s' -> l1 s s' c1_s_s'
\end{verbatim}
    
4. for while, we are essentially checking i is a legitimate loop invariant

\begin{verbatim}
    {-@ lem_while :: b:_ -> c:_ -> p:_ 
                -> Legit (bAnd p b) c p 
                -> Legit p (While b c) (bAnd p (Not b)) 
    @-}
    lem_while :: BExp -> Com -> Assertion -> Legit -> Legit 
    lem_while b c p lbody s s' (BWhileF {}) 
    = ()
    lem_while b c p lbody s s' (BWhileT _ _ _ smid _ c_s_smid w_smid_s') 
    = lem_while b c p lbody (smid ? lbody s smid c_s_smid) s' w_smid_s' 
\end{verbatim}    

Let's look at some examples:

Example 1:

\begin{verbatim}
    ex1   :: () -> ()
    ex1 _ = verify p c q (\_ -> ()) 
    where 
        p = tt                                    -- { true } 
        c = IAssign "x" (N 5)                    --    x := 50
        q = Equal (V "x") (N 5)                   -- { x == 5 }
\end{verbatim}

We found that
    -- p    => pre c q /\ vc c q
    -- VC  = (True => 5 = 5) /\ True 
    -- pre = 50 == 5

Example 2:

\begin{verbatim}
    ex2   :: () -> () 
    ex2 _ = verify p c q (\_ -> ()) 
    where 
        p = Equal (V "x") (N 2)                   -- { x = 2 } 
        c = IAssign "x" (Plus (V "x") (N 1))      --    x := x + 1
        q = Equal (V "x") (N 3)                   -- { x = 3 }

        --        p    => pre c q /\ vc c q
        -- VC  = (x=2 => x+1=3) /\ True 
        -- pre = x+1 = 3 
\end{verbatim}

Example 3:

\begin{verbatim}
    bx2 :: () -> () 
    bx2 _ = verify p c q (\_ -> ()) 
    where 
        p =      (V "x" `Equal` V "a") 
        `bAnd` (V "y" `Equal` V "b")                -- { x = a && y = b } 
        c =      IAssign "x" (Plus  (V "x") (V "y"))  --     x := x + y
        `ISeq` IAssign "y" (Minus (V "x") (V "y"))  --     y := x - y
        `ISeq` IAssign "x" (Minus (V "x") (V "y"))  --     x := x - y
        q =      (V "x" `Equal` V "b")                -- { x = b && y = a } 
        `bAnd` (V "y" `Equal` V "a") 

        -- vc' = x=a & y=b => (x+y-(x+y-y) =b && (x+y)-y=a) && true & True & true
        -- pre = (x+y-(x+y-y) =b && (x+y)-y=a)
        -- vc  = true & true & true 
\end{verbatim}

Example 4:

\begin{verbatim}
    ex10  :: () -> () 
    ex10 _ = verify p c q (\_ -> ()) 
    where 
        p = Equal (V "x") (N 1)                    -- { x = 1 } 
        c = IWhile i (Not (Leq (V "x") (N 0)))     --   WHILE (x > 0) DO
            (IAssign "x" (Plus (V "x") (N 1)))   --     x := x + 1
        q = Equal (V "x") (N 100)                  -- { x = 100 } 
        i = undefined -- TODO: In class

        -- P => I 
        -- {I && b} c { I }
        -- I && !b => Q 
            -- x>0 &&& not ( x > 0 ) => Q
        -- I := x > 0 
\end{verbatim}

Example 5:
\begin{verbatim}
    ex9  :: () -> () 
    ex9 _ = verify p c q (\_ -> ()) 
    where 
        p = Equal (V "x") (N 0)                    -- { x = 0 } 
        c = IWhile i (Leq (V "x") (N 0))           --   WHILE_i (x <= 0) DO
            (IAssign "x" (Plus (V "x") (N 1)))   --     x := x + 1
        q = Equal (V "x") (N 1)                    -- { x = 1 } 
        i = bOr p (Equal (V "x") (N 1))

        -- x=0 => (x=0 || x=1)
        -- {(x=0 || x=1) /\ x <= 0 } x := x+1 {x=0 || x=1}
        -- (x=0|| x=1) /\ x > 0 => x = 1
\end{verbatim}

--note: In final exam, we will prove soundness of vc and we will do it in two steps.