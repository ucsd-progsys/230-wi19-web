\begin{code}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_3_6 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import qualified Data.Set as S
import           Expressions hiding (And)
import           Imp 
import 	         BigStep

\end{code}

"AXIOMATIC SEMANTICS" 

Floyd-Hoare Triples 
===================

A Floyd-Hoare triple is of the form 

        { P }  c { Q }

where 
      
- `P` and `Q` are assertions (think `BExp`) and 
- `c` is a command (think `Com`) 


What does it MEAN for {P} c {Q} to hold?

    let s = "starting" state
    let s' = "after you execute" c the state s "transitions to" s'

\begin{code}
{-@ type Legit P C Q = s:_ -> s':_ -> { bval P s } -> (BStep c s s') -> { bval Q s' } @-}
\end{code}


1. {True}  
     X <~ 5 
   {X = 5}


2. {X = 2} 
     X <~ X + 1 
   {X = 3}



3. {True}  
     X <~ 5; 
     Y <~ 0 
   {X = 5}

4. {True}  
        X <~ 5; 
        Y <~ X 
   {Y = 5}


Legit P C Q? 

type Legit P C Q = s:_ -> s':_ -> { bval P s } -> (BStep c s s') -> { bval Q s' }

5. {X = 2 && X = 3} 
        X <~ 5 
   {X = 0}

    LEGIT

6. {True} 
     SKIP 
   {False}

    NOT-LEGIT 

7. {False} 
     SKIP 
   {True}
    
    LEGIT 






type Legit P C Q = s:_, s':_ . IF bval P s && BStep c s s' THEN  bval Q s' 

6. {True} 
     SKIP 
   {False}

    NOT-LEGIT 

8. {True} 
        WHILE True DO 
          SKIP 
   { False } 

9.
   {False}
        SKIP
   {False}


    LEGIT

    NOT-LEGIT


10. {X = 0}
        WHILE X <= 0 DO 
          X <~ X + 1 
    {X = 1}


11. {X = 1}
         WHILE (X > 0) DO 
           X <~ X + 1 
    {X = 100}


    LEGIT

    NOT-LEGIT





A Floyd-Hoare triple states that 

IF 

* The program `c` is starts at a state where the *precondition* `P` is True, and 
* The program finishes execution

THEN 

* At the final state, the *postcondition* `Q` will also evaluate to True.

Lets paraphrase the following Hoare triples in English.

1. `{True}   c {X = 5}`

2. `{X = m}  c {X = m + 5}`

3. `{X <= Y} c {Y <= X}`

4. `{True}   c {False}`


The type `Assertion` formalizes the type for the 
assertions (i.e. pre- and post-conditions) `P`, `Q`
appearing in the triples {P} c {Q}

\begin{code}
{-@ type Legit P C Q = s:_ -> s':_ -> { bval P s } -> (BStep c s s') -> { bval Q s' } @-}
type Assertion = BExp 

type Legit = State -> State -> BStep -> Proof 

{-@ lem_skip :: p:_ -> (Legit p Skip p) @-}
lem_skip :: Assertion -> Legit 
lem_skip p = \s s' (BSkip {}) -> () 


{-@ lem_asgn :: x:_ -> a:_ -> q:_ -> (Legit (bsubst x a q) (Assign x a) q) @-}
lem_asgn :: Vname -> AExp -> Assertion -> Legit
lem_asgn x a q = \s s' (BAssign {}) -> () 


\end{code}