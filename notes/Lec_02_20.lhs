{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_20 where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions hiding (And)
import           Imp 




In this lecture, we reviewed some basic concepts from weeks 4 and 5 in order to clarify 
any confusion on the differneces between "proofs" and "props". This lecture covered: 

0. What is Prop exactly? Why aren't we using Proofs anymore?
1. Even peano numbers
2. Relations and the relation graphs
3. A re-introduction to big step semantics, and how to represent props as operational semantics-y 
proofs  


0. Prop versus Proof 

A prop, defined in liquid haskell, is just a dummy type wrapper we use as a datastructure to 
represent "inductive propositions". We will see how we can use it to implement proof trees. 
It is defined as: 

{-@ measure prop :: a -> b @-}
{-@ type Prop P = {v:_ | prop v = P} @-}

Note that this is a liquid haskell construct. The GHC does not know what a prop is. "type Prop" doesn't look like 
it's doing much because it isn't. It's basically a wrapper. If "some_type" is a type that denotes a property 
or state (like that a number is even), we read, for the sake of writing these proofs,

"Prop (some_type)"

As "A proof of some_type". Let's see a concrete example with evenness: 


--------------------------------------------------------------------------------
-- | Defining "Even Numbers"
--------------------------------------------------------------------------------

data Peano = Z | S Peano

-- | The "Prop" describing an Even number `(Ev n)`

data EvProp where
  Ev :: Peano -> EvProp

-- | The ways to "construct evidence" of evenness i.e. that "prove" `Ev n`

data EvProof where
  EvZ :: EvProof
  EvS :: Peano -> EvProof -> EvProof

Per usual we defined "Peano" as a Z or the successor of another Peano. However, in GHC we defined new datatypes.

EvProp takes in a peano, and outputs an "EvProp". We will later read this as "A proof that Peano is Even"
 
A data type called EvProof. It looks like there are two ways of constructing an EvProof: an EvZ is 
an EvProof, and an EvS is also an EvProof. EvZ is just an alias for an EvProof, i.e. it is not a function. 
Zeros are just even. EvS takes in a Peano, a proof that something is even, and outputs another proof that 
something is even. Mysterious. Note that this datatype was created for the GHC, and doesn't really mean 
much on its own. Liquid haskell annotations will help us make it meaningful. 

-- 
-- type Prop E = {v:_ | prop v = E}

{-@ data EvProof where
      EvZ :: Prop (Ev Z)
    | EvS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))
  @-}

The liquid annotation of EvProof is a little more interesting. We see that EvZ is just an alias for 
Prop (Ev Z). We unfold this is as:

"EvZ is just an alias for Prop (Ev Z)"
"EvZ is just an alias for the proof that "Ev Z"
"EvZ is just an alias for the proof that zero is even"

For EvS, we can do the same thing. 

"EvS is a function that takes a peano n, a Prop (Ev n), and outputs a Prop (Ev (S (S n)))"
"EvS is a function that takes a peano n, the proof that Ev n, and outputs the proof that Ev (S (S n))"
"EvS is a function that takes a peano n, the proof that n is even, and outputs a proof that S (S n) is even"

We can see how these inductive proof datatypes can resemble a classic proof tree:

{- | Read the above as there are two "rules" to determine even-ness


      ------------------ [EvZ]
         Ev Z


         Ev n
      ------------------ [EvS]
         Ev (S (S n))

 -}


Below are some examples of how to use this in a proof. 


{-@ zero_is_Even :: {pf:EvProof | prop pf == (Ev Z) } @-}
zero_is_Even :: EvProof 
zero_is_Even = EvZ

{-@ two_is_Even :: {pf : EvProof | prop pf = (Ev (S (S Z))) } @-}
two_is_Even :: EvProof  
two_is_Even = EvS Z zero_is_Even

{-@ four_is_Even :: Prop (Ev (S (S (S (S Z))))) @-}
four_is_Even :: EvProof  
four_is_Even = EvS (S (S Z)) two_is_Even



Note that we do not use the (===), (&&&), (*** QED) or those other equivalence 
things for these proofs. Those proofs unfolded definitions to proof postcondition predicates: that is, 
since the outputs were postconditions of the form {v:_ | predicate}, algebra could be used to show 
equivalences. Those proofs did not recursively build proof trees. This is a different proof technique 
that proves that properties hold. We can note the difference of what kind of proof we need to use by the 
postcondition in liquid haskell: 

blahblah -> {v:_ | predicate}   use the (===) guys for this
blahblah -> Prop (some_type)    need to use "inductive proposition" technique 



-----------------------------------------------------------------------
-- Relations
type Rel a = a -> a -> Bool

-- | The Prop describing the closure of a relation
data PathProp a where
  Path :: Rel a -> a -> a -> PathProp a

-- | The Proof of the existence of a path ... 
data PathProof a where
  Refl :: Rel a -> a -> PathProof a
  Step :: Rel a -> a -> a -> a -> PathProof a -> PathProof a

{-@ data PathProof a where
      Refl :: r:Rel a -> x:a -> Prop (Path r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Path r y z) -> Prop (Path r x z)
  @-}

--------------------------------------------------------------------------------

-- x -> ... -> y        y -> ... -> z
--------------------------------------
-- x -> ... -> z


A relation is a subset of the ordered pairs between two sets, but for this class we generally 
don't need to know that. We represent relations as a type Rel a -> a -> Bool, which reads 

Rel x y = True if x and y are related

The proofs on homework 4 involving relations involve showing that there exists a "path" between
two elements, such that a path is defined as a chain of relations in a graph. The above definition
of PathProof is inductive. It states:

Given points

x   y   z 

there is a path from x to z if there if x and y are "related", and if there is already a path 
from y to z (we use induction here).  


--------------------------------------------------------------------------------
-- | Big-step Semantics 
--------------------------------------------------------------------------------

{- BIG Step Semantics 

  BStep c s s'


  ------------------[BSkip]
    BStep Skip s s


  ------------------------------------------[BAssign]
    BStep (x := a) s (set s x (aval a s))


    BStep c1 s smid    BStep c2 smid s'
  ----------------------------------------[BSeq]
    BStep (c1; c2) s s' 


    bval b s = TRUE      BStep c1 s s'
  ----------------------------------------[BIfT]
    BStep (If b c1 c2) s s' 


    bval b s = FALSE     BStep c2 s s'
  ----------------------------------------[BIfF]
    BStep (If b c1 c2) s s' 


    bval b s = TRUE      
    BStep c s smid  
    BStep (While b c) smid s'   
  --------------------------------------------------[BWhileT]
    BStep (While b c) s s' 

    bval b s = FALSE      
  ----------------------------------------[BWhileF]
    BStep (While b c) s s

 -}



Big-step semantics, or natural semantics, are a subset of Operational semantics, and describe 
the behavior of the overall program (determed by the results of the executions). The proof trees
above are defined for a simple imperative language that was introduced in previous lectures.


BSkip is an axiom. It takes in the current state, and outputs the current state i.e. it does nothing. 

BAssign is also an axiom. It takes the current assign command and the current state, and outputs the 
next state as [current state with new variable definition] 

BSeq is given two commands. It asserts that if command 1 executes in state s to yield s-mid, and command 2 executes
in s-mid to yield s', then you can sequentially execute (c1;c2) in state s to yield s'.

We split BIf into the true and false cases. BIfT should read "given b evalues to true and steping (c1 s) -> s'", then 
the entire expression evaluates to s'. BIfF is similar, but evaluates with the second branch c2. 

While is tricky. Again, we must case split on true and fales cases (for when the loop condition "b" is true or false). 
However, because this command is less trivial than the If case splits, we will unpack the whole thing for an explanation:

BStep (While b c) s s' reads "Stepping the command (While b c) in state s yields s'"

The command (While b c) contains the loop condition b, and the loop commands c. Given that b evalues to true (BWhileT),
and that the loop commands c (when evaluated in state s) yield intermediatry state "smid", and that the entire command 
(While b c) evaluates to s' in smid, then (While b c) evaluates in s to s'. This formalizes the notion that if the loop
condition b holds, then command will evaluate to a new state s' determined by the loop commands c. On that note, we see 
that the rule BWhileF dictates that if the loop condition b is false, then the output state is no different than the input 
state (that is, the loop commands c have no impact on our output state).  

The BStep, or Big Step, takes in a command (from IMP), a current state, and outputs the next state.
These formal semantics only care about what the output state of the program is, hence why they are big 
step. 
  



data BStepProp where
  BStep :: Com -> State -> State -> BStepProp 

data BStepProof where 
  BSkip   :: State -> BStepProof 
  BAssign :: Vname -> AExp -> State -> BStepProof 
  BSeq    :: Com   -> Com  -> State -> State -> State -> BStepProof -> BStepProof -> BStepProof 
  BIfT    :: BExp  -> Com  -> Com   -> State -> State -> BStepProof -> BStepProof  
  BIfF    :: BExp  -> Com  -> Com   -> State -> State -> BStepProof -> BStepProof
  BWhileF :: BExp  -> Com  -> State -> BStepProof 
  BWhileT :: BExp  -> Com  -> State -> State -> State -> BStepProof -> BStepProof -> BStepProof 

{-@ data BStepProof where 
      BSkip   :: s:_ 
              -> Prop (BStep Skip s s)
    | BAssign :: x:_ -> a:_ -> s:_
              -> Prop (BStep (Assign x a) s (asgn x a s)) 
    | BSeq    :: c1:_ -> c2:_ -> s1:_ -> s2:_ -> s3:_
              -> Prop (BStep c1 s1 s2) 
              -> Prop (BStep c2 s2 s3) 
              -> Prop (BStep (Seq c1 c2) s1 s3)
    | BIfT    :: b:_ -> c1:_ -> c2:_ -> s:{_ | bval b s} -> s1:_
              -> Prop (BStep c1 s s1) 
              -> Prop (BStep (If b c1 c2) s s1)
    | BIfF    :: b:_ -> c1:_ -> c2:_ -> s:{_ | not (bval b s)} -> s2:_ 
              -> Prop (BStep c2 s s2) 
              -> Prop (BStep (If b c1 c2) s s2)
    | BWhileF :: b:_ -> c:_ -> s:{_ | not (bval b s)} 
              -> Prop (BStep (While b c) s s)
    | BWhileT :: b:_ -> c:_ -> s1:{_ | bval b s1} -> s1':_ -> s2:_
              -> Prop (BStep c s1 s1') 
              -> Prop (BStep (While b c) s1' s2)
              -> Prop (BStep (While b c) s1 s2)
  @-}  


--------------------------------------------------------------------------------


The above formalizes these notions the same way Ev formalized our intuition of the Evenness 
proof trees. The important takeaway of these is that each rule (BAssign, BSeq, etc.) takes in

0. A collection of the variables that will be used, because GHC will get confused if x, a, s, etc.
are not defined as separate inputs

1. Proofs of the pre-conditions in terms of Props. These are Props of what is said on the "top half" 
of the line

2. Output a proof (in the form of a Prop) that should go on the bottom of the proof line  




-- x := 5
{-@ reflect cmd_1 @-}
cmd_1 = "x" <~ N 5

-- y := x
{-@ reflect cmd_2 @-}
cmd_2 = "y" <~ (V "x")

-- x := 5; y := x
{-@ reflect cmd_1_2 @-}
cmd_1_2 = cmd_1 @@ cmd_2 

{-@ reflect prop_set @-}
prop_set cmd x v s = BStep cmd s (S.set s x v)


-- BStep (x := 5) s (S.set s x 5)
{-@ step_1 :: s:State -> Prop (BStep (Assign {"x"} (N 5)) s (S.set s {"x"} 5)) @-}
step_1 s =  BAssign "x" (N 5) s



{-@ step_2 :: s:{State | S.get s "x" == 5} -> Prop (prop_set cmd_2 {"y"} 5 s) @-}
step_2 s = BAssign "y" (V "x") s

{-@ step_1_2 :: s:State -> Prop (BStep cmd_1_2 s (S.set (S.set s {"x"} 5) {"y"} 5)) @-}
step_1_2 s = BSeq cmd_1 cmd_2 s s1 s2 (step_1 s) (step_2 s1) 
  where 
    s1     = S.set s  "x" 5 
    s2     = S.set s1 "y" 5

{- 
{-@ lem_semi :: c1:_ -> c2:_ -> c3:_ -> s:_ -> s3:_
      -> Prop (BStep (Seq (Seq c1 c2) c3) s s3)
      -> Prop (BStep (Seq c1 (Seq c2 c3)) s s3) 
  @-}
lem_semi :: Com -> Com -> Com -> State -> State -> _ -> _
lem_semi _ _ _ s s3 (BSeq c12 c3 _ s2 _ (BSeq c1 c2 _ s1 _  bs1 bs2) bs3) 
  = BSeq c1 (Seq c2 c3) s s1 s3 bs1 (BSeq c2 c3 s1 s2 s3 bs2 bs3)

-}


The proofs above show how we can use the precondition props to inductively arrive at the postcondition 
props. This is the nature of proofs by "inductive propositions". Instead of unfolding function definitions 
with the help of (===), we unfold the properties themselves. Let's look at the last one (lem_semi), which defines 
the notion that sequences of instructions are somehow "associative"

that is, 

(c1;c2);c3 is the same as c1;(c2;c3)

We prove this "sameness" in terms of big step semantics. By that, I mean that given an initial state s, activating 
(c1;c2);c3 puts us in the same state as if we had evaluated c1;(c2;c3). This is equality "in terms of" big step semantics
in that we are definition equality soley based on the output behavior of the program. If they give us the same output, they
are the same thing.

lem_semi formalizes this "associativity" by trying to prove: 

If Stepping Seq ((Seq c1 c2) c3) over s gives us s3, then
Stepping Seq (c1 Seq (c2 c3)) over s gives us the same state. 

lem_semi takes in a lot of inputs and has a lot of symbols, and otherwise looks scary. We will break things down piece by 
piece and recombine to show that it is not, in fact, that scary. 

First, let's look at the left hand side, which represents what we are given, that is (c1;c2);c3 in s ~> s'

_ _ _ s s3 (BSeq c12 c3 _ s2 _ (BSeq c1 c2 _ s1 _ bs1 bs2) bs3)

Which we can line up with lem_semi's type declaration:

Com -> Com -> Com -> State -> State -> _ -> _

Okay, we are given the first three underscores as commands. These will obviously be c1, c2 and c3 in our proof. Similarly, 
s and s3 will be our given and final states. They are mostly included as input for the lemma so GHC does not yell at us 
if we use those symbols later (which, in the case of s and s3, we will). c1, c2 and c3 are blanked out because we will 
prefer to define them and further refer to them in the sequency terms later.

The commnds and states out of the way, the last input here is a proof: (BSeq c12 c3 _ s2 _ (BSeq c1 c2 _ s1 _ bs1 bs2) bs3)
This is the meat of the input, the part we really care about: it is "what's on the top of the line" in the proof tree. 


Inner proof: BSeq c1 c2 _ s1 bs1 bs3 is a proof that, if c1 steps (in _) to s1 (proved axiomatically by bs1), and 
c2 steps (in s1) to _ (proved axiomatically by bs2), then the sequence (c1;c2) steps in _ to _.

Outer proof: The outer BSeq stats that if c1c2 steps (in _) to s2, and c3 steps (in s2) to _, then (c1;c2);c3 steps in _ to _. Note that 
the proof of the first statement (That c1c2 steps in blah) is given explicitly by our nested BSeq statement, while the proof 
of the seocnd is given axiomatically by "bs3".   

Turning to our ouput now:

BSeq c1 (Seq c2 c3) s s1 s3 bs1 (BSeq c2 c3 s1 s2 s3 bs2 bs3)

We inductively use our proofs from the input (bs1, bs2, bs3) to show that c1;(c2;c3) s ~> s3

The line can be read explicitly as:

Stepping c1 in s gives s1, and stepping (Seq c2 c3) in s1 gives s3. The proof bs1 is given to us in the input, which we already discussed:
stepping c in _ will give s1. the second proof is given explicitly: stepping c2 in s1 gives s2, stepping c3 in s2 gives s3, using the inductive 
proofs bs2 and bs3 already given to us.
