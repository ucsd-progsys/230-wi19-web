### CSE 230: Programming Languages
### Winter 2019
### Monday, February 11
##### Instructor: Ranjit Jhala
##### Scribe: Nemil Shah and Sourav Anand

--- Revision of Week 4

We looked at various examples of inductive predicates such as Palindrome, and isEven.

Now we will look into the 'AExp' example. To give meaning to this expression we wrote a function that evaluates the expression.

Next, we'll look at more complex data objects. We will look at a language that looks like this.

data Com
 = Skip						
 | Assign Vname AEcp		
 | Seq Com Com				
 | If BExp Com Com 			
 | While BExp Com 			
 deriving (Show)

It'a a very small Impertaive Prograaming Language.

We cannot write an eval function for this because a 'while' loop can run forever. In comparison to AExp, when given a state the eval function can always evaluate the value of this expression. However this is not true for the 'Com' expressions because of the 'while' loops.

Let's write a 'cval' function that takes 'Com' expression and a state as input and tries to produce an output state.


Let us look into the way to define the behavior of Arithmetic Expressions using Inductive Predicates. The AExp is defined as follows :-

type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 
  deriving (Show)

Some of the Relations we've seen so far.
1. Ev n
2. Pal xs

These are were unary relations as they all take one input. We want to write a relation that takes an 'Aexp a', 'State s', and a 'Number n' such that 'a' evaluates to 'n' starting from state 's'. We will call this relation AvRel.

-- AvRel s a n

We will define AvRel from scratch as a proof system, similar to what we saw with the Even Peanos. AExp consists of three definitions, namely, a number, a variable and a plus operation. We will have to define rules for each of them.

Rule 1 corresponds to a Number -- AExp a == (N n)
			
	----------------------- [AvRelN]
		AvRel s (N n) n


Rule 2 corresponds to a Variable -- AExp a == (V x)
			
		get s x == n
	----------------------- [AvRelV]
		AvRel s (V x) n


Rule 3 corresponds to a Plus -- AExp a == (Plus a1 a2)
			
		(AvRel s a1 n1) (AvRel s a2 n2) (n == n1 + n2) 
	----------------------------------------------------	[AvRelP]
			AvRel s (Plus a1 a2) n

							OR

		(AvRel s a1 n1)  (AvRel s a2 n2)
	----------------------------------------------------	[AvRelP]
			AvRel s (Plus a1 a2) (n1 + n2)


-- Side note. 
We cannot have something like this in the numerator:
AvRel a1 s + AvRel a2 s == n
This is because AvRel returns a 'Bool' and not a 'Number' for us to evaluate.


The following is the code that defines AvRel and the 3 rules we've written above.

-- | The Prop declaring the AvRel predicate 
data AvRelP where
  AvRel :: State -> AExp -> Val -> AvRelP 

{-@ data AvRel where
      AvRelN :: s:_ -> n:_ 
      		-> Prop (AvRel s (N n) n) 
    | AvRelV :: s:_ -> x:_ 
    		-> Prop (AvRel s (V x) (S.get s x)) 
    | AvRelP :: s:_ -> a1:_ -> n1:_ -> a2:_ -> n2:_ 
            -> Prop (AvRel s a1 v1) 
            -> Prop (AvRel s a2 v2)
            -> Prop (AvRel s (Plus a1 a2) {n1 + n2})
 @-}


We will now define a theorem to prove for any state and any expression s.t.
-- forall s,a
	 AvRel s a (aval a s)

The two directions for this theorem are,
1. s:_ -> a:_ -> n:{ n = aval a s } -> Prop(AvRel s a (aval a s))
To prove that, for any state s, AExp a, and a Number n, the property Prop(AvRel s a (aval a s)) holds.


2. s:_ -> a:_ -> n:_ -> Prop(AvRel s a (aval a s)) -> { n = aval a s }
To prove that, for any state s, AExp a, and a proporty Prop(AvRel s a (aval a s)), then 'aval a s' should evaluate to 'n'.


Lemma to prove 2.

{-@ lem_avrel :: s:_ -> a:_ -> n:_ -> Prop(AvRel s a (aval a s)) -> { n == aval a s } @-}
lem_avrel :: State -> AExp -> Val -> AvRel -> Proof
lem_avrel s (N n)        _n (AvRelN {}) = ()
lem_avrel s (V x)        _  (AvRelV {}) = ()
lem_avrel s (Plus a1 a2) _  (AvRelP _s _a1 n1 _a2 n2 p_a1_n1 p_a2_n2)
										=   lem_avrel s a1 n1 p_a1_n1 --- aval a1 s == n1
										&&& lem_avrel s a1 n2 p_a2_n2 --- aval a2 s == n2

lem_avrel s _ _ _ = impossible " "


Let's now jump to the complex data type 'Com' and see how we can write rules like AvRel for this language.

'Com' consists of the following :-
data Com
 = Skip						-- Skip/ NOP
 | Assign Vname AEcp		-- x := a
 | Seq Com Com				-- do c1; (followed by) c2
 | If BExp Com Com 			-- if b then do c1 else do c2
 | While BExp Com 			-- while b do c
 deriving (Show)



We have if and while statements in Com which contains a Boolean expression. We need a grammar for Boolean expressions which is defined as follows :-

data BExp 
  = Bc   Bool 				-- True, False
  | Not  BExp 				-- not b
  | And  BExp BExp 			-- b1 && b2
  | Less AExp AExp 			-- a1 < a2
  deriving (Show)


We cannot define a cval for 'Com' as established above. We will try to define relations using Big Step Semantics.

Relations says - After executing <command c, starting at state s> --> We end up in <state s`>. 

We are now dealing with commands instead of Expressions as from previous weeks. 

BStemp c s s`
The above expression means that if you start at state s, execute c, you can end up at state s`.

The proof tree for the above relation is shown below. We will have several rules to account for the various commands in 'Com'.


{-

	------------------------------------------- [BSkip]
		BStep Skip s s

	-- Skip does nothing so s == s` == s



		BStep c1 s smid 	BStep c2 smid s`	
	-------------------------------------------	[BSeq]
		BStep (c1; c2) s s`

	-- Based on start at state s -> run c1 -> go to smid -> execute c2 -> end at state s`



		s` = set x (aval a s) s
	------------------------------------------- [BAssign]
		BStep (x := a) s s`

	-- We have to evaluate 'AExp a' first before assigning it to x.



		bval b s = TRUE 	Bstep c1 s s`
	------------------------------------------- [BIfT]
		BStep (If b c1 c2) s s`

	-- We have to evaluate the Boolean expression 'b' first and then have two separate case for each value, i.e. True and False

		bval b s1 = FALSE 	BStep c2 s s`
	-------------------------------------------	[BIfF]
		BStep (If b c1 c2) s s`



-}

We will look at the rule for while in the next class.






