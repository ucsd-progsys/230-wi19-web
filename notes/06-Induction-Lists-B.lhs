--Scribe Notes taken by Stewart Grant Jan_28_2019
--Two part transctiption:
--1) Board Notes recorded in haskell + liquid haskell
--2) Audio Notes recored by Shu-Ting Wang, transcribed by Stew.


--this is how you prove that append is associative,
--if you have three lists we want to prove that one is equal to another
--we want to prove that (xs + ys) + za is the same as xs + (ys + zs)
--Last time:

--We take the goal l1 l2 and l3, and we define the goal as impossible, we first
--want to do some case splitting on the first argument l1, split on it being
--either nil, or (Cons x xs), and the other list y z.

--the other thing that we did, was once we figured out what our goals are we plug
--in the values of l1, l2 and l3 as our goals. This is the same thing we did last
--time. First we prove our trivial case, then we move on to our more complicated
--cases.

--Now note that this equality does not just hold, we need to apply the lemma in
--the middle, because the equality does not just hold.

--And now look at the last step, n


--Audrey) if it gives you an error at a prior line, does it mean that the error may
--have happened at a later line? Ranjit ) Yes the errors are reported at the first
--sign of failure.

--Now how do we know that two things are equal? Well we can use the induction hypothesis, so we can make a recursive call.

--Its should take a list of A's and return a list of A's
rev:: List a -> List a
rev (Cons 1 (Cons 2 (Cons 3 Nil ))) == Cons 3 ( Cons 3 ( Cons 1 Nil)))


--There are two ways that this list can be taken


--Now as it happens you can tell liquid Haskell every time you see the unfolding
--of a function you can just tell liquid Haskell, just unfold it for me,
--(instantiate tool) this unfortunately is unpredictable. In order to do this you
--need to turn on a function called PLE

--with PLE you can comment out all of the intermediate steps, really the undeceive
--proof just becomes this.. Now while you are doing the homework you can turn on
--PLE in order to reduce the work done by unfolding all of the function
--definitions.

--Now we are going to introduced a reverse function.
--
rev:: List a -> List a
rev Nil     = Nil
rev (Cons x xs) = app (rev xs) x undefined`

x xs        ---> (rev ex) `app` (Cons x Nil) 
1 [2,3,4] --> app [4,3,2] [1]

--Now someone asked a question on piazza, Why are we getting a recursion error,
--because we are not working on a smaller list. If you do not recur on a smaller
--list then the formula may never terminate.

--My daughter wants to eat chocolate because she wants to eat chocolate.



rev (Cons x xs) = app (rev xs) -- x undefined note that we cannot append simply the element x because x is not a list


--There are two ways to define a list, the first of which is the Nil case (left
--to the members of the class.

-- This is lines 54-59 from the notes

--We essentially made the list rev xs's and stuck the list with Nil at the end.
--Note here that x is not a list it is a single element so we cannot append it
--because it is not well typed, instead we are going to return (Cons x Nil)
--instead. 

--I'm going to prove a silly theorem instead: the theorem states that if I reverse a list

--x,y,z it should be the same as if i  return the list z,y,x

--we encounter the error message unbound symbol, rev. This just means that we
--need to do to bring the definition of rev into the theorem.

--PLE) Think of PLE as, it's not the worst example in the world, okay first of all
--if I switch off PLE I'm going to get a type error, so lets first write a proof
--of why this statement should be true.

--First lets prove something on x,y,z. Now if we pass it to PLE the proof gets
--unfolded automatically, how would we prove this if it was just us making the
--proof. How? MJ- we can just unfold the definition of reverse. (proceed to unfold
--the definition of rev. Now if we want to continue with this patter to complete
--the proof we need to unfold the definition of rev again.

--This rev of Nil is actually equal to (Cons x Nil) -- Ranjit battles with a
--bunch of bugs, the error was a capitol Z.
--
rev:: List a -> List a
rev Nil     = Nil
rev (Cons x xs) = app (rev xs) (Cons x Nil)


-- imagine the possible formula 

{-@ foo :: x:_ -> y:_ ->z:_ -> { rev (Cons x ( Cons y ( Cons x Nil ) ) ) == Cons z ( Cons y ( Cons x Nil ) ) ) @-}
foo :: a -> a -> a -> Proof
foo _ _ _ = ()


--if we want to make an automatic proof on this we can perform recursion
--automatically by unfolding the definition of the function using reflect

{-@ reflect foo @-}
rev:: List a -> List a
rev Nil     = Nil
rev (Cons x xs) = app (rev xs) (Cons x Nil)

--now we are going to do the proof manually using the class cookbook without using
--the reflect library as a means to understand why the reflect library should be
--used in the first place


--Now we have to run the definition of append a bunch of times, I'm just running
--the program here, there is nothing exciting here, (Its' really basic, if you
--want to make a proof just unfold the definition of the function a bunch of times.
--Just apply append to this list, and then again to the next list.

--Q is there some depth that PLE will terminate at?
--A) No PLE is unbounded there is no depth that PLE will stop at.

--Q)Basically if you can unroll a definition that is what PLE will do for you?
--A) Yes, I know what rev does, so each time you see rev apply rev. 

--Q) Does that include the theorem you are currently trying to prove
--A) No. It only includes function definitions.

--Q) So how do you turn on PLE again
--A) ** Ranjit fumbles with liquid Haskell -- If you actually went though all of the steps it would be useful.

{-@ foo :: x:_ -> y:_ ->z:_ -> { rev (Cons x ( Cons y ( Cons x Nil ) ) ) == Cons z ( Cons y ( Cons x Nil ) ) ) @-}
foo :: a -> a -> a -> Proof
foo x y z = ()
    = rev (Cons X ( Cons y ( Cons z Nil) ) )
    === rev (Cons y ( Cons Z Nil ) `app` (Cons x Nil) 
    === ( rev (( Cons z Nil )) `app` (Cons y Nil) ) `app` (Cons x Nil)
    === ( rev Nil ) `app` (Cons z Nil) `app` (Cons y Nil) ) `app` (Cons x Nil) 
    === ( Nil `app` (Cons z Nil) `app` (Cons y Nil)) `app` (Cons x Nil)
    === ( ( Cons z Nil ) `app` ( Cons y Nil) 


--This is just an illustration of how to unwrap functions, and the operations
--which can be performed by recursively applying the definitions of functions.


--Q) how do you pass this to PLE again?
--A) 

--Note :: Often a useful procedure is to work thought the steps manually and
--then automatically verify the program using PLE for conciseness
--calling reverse twice on the same list returns the same list therefore
--
--So now lets try to prove this.

--Lets say that we have a list x1, x2, x3 and I reverse it I get x3, x2, x1.
--but if I reverse it again I get, x1, x2, x3.

-- I'm going to define a theorem called rev_rev
--It should take a list of a's and return a proof.

--It should have two cases one is Nil. This is simple: Rev of Nil is Nil.

--To prove this we are going to use our usual strategy, we are going to prove
--Line (80). What do we do? We want to reverse a cons. by the definition of rev,
--rev the list and then append the list of Cons x Nil. (Laughter). (Errors)

--How should we proceed here. Sometimes I cannot think while I'm typing. Here we
--are going to use the whiteboard

--line 89) The step that we are stuck on looks something like this. Rev xs, with
--your permission I'll write it in this infix style. rev of one list appended to
--another is just the list append to another. Here the list x cons x is just the
--list. Why does this equality hod, we know that it holds, what do we need over
--here? There is something that requires the append operator and the rev
--operator. What do we need here?

--Michael ) Append distributes rev across the elements of the list. Now lets say
--that we have two list a and b

{-@ thm_rev_rev :: xs: _ -> { rev (rev xs ) == xs } @-}
thm_rev_rev Nil
 = rev (rev Nil) === Nil *** QED

thm_rev_rev (Cons x xs)
 = rev (rev (cons x xs)) // how do we reverse a Cons ?
 === rev ( rev xs `app` (Cons x Nil) )
 === Cons x xs
 *** QED

--running this code resulted in a huge endless stack overflow. How do we continue
--from here and why did the recursive definition cause the program to loop
--forever?

-- Chalkboard
--rev ( rev xs H [ X ] )
--
--rev ( rev xs H [ X ] )
---   ------   -----
--         A       B

-- Bask in liquid haskell

rev ([a1,a2,a3] ++ [b1,b2,b3])
rev ([a1,a2,a3,b1,b2,b3])
== [b3,b2,b1,a3,a2,a1]
rev (as ++ bs) 

{-@ thm_reb_app :: as:_ -> bs_ -> { reb (app as bs ) == app (rev bs) (rev as) } @-}
thm_rev_app :: List a -> List a -> Proof
thm_rev_app = undefined

--Now continuing back to where we were before

-- We are taking these two lists and we are distributing their
--concatenation. We are appending the rev of the a's to the rev of the bs.


--But now what your saying, this is all of the b's backward and this is all of
--the a's backwards, what we are actually saying is that rev for as plus bs is
--equal to rev of a's plus rev of bs. So if we add this what would happen?

them_rev_rev (Cons x xs)
 = rev (rev (cons x xs)) // how do we reverse a Cons ?
 === rev ( rev xs `app` (Cons x Nil) )
    ? thm_rev_app (rev sx) (Cons x Nil)
 === (rev (Cons x Nil)) `app` (rev (rev xs))
   ? thm _rev_rev xs
 === Cons x xs
 === Cons x xs
 *** QEd

-- Now that we are using the automatic induction tool we no longer require much of the proof


thm_rev_rev (Cons x xs)
 = rev (rev (cons x xs)) // how do we reverse a Cons ?
-- === rev ( rev xs `app` (Cons x Nil) )
    ? thm_rev_app (rev sx) (Cons x Nil)
-- === (rev (Cons x Nil)) `app` (rev (rev xs))
   ? thm _rev_rev xs
-- === Cons x xs
-- === Cons x xs
-- *** QED

--But now what your saying, this is all of the b's backward and this is all of
--the a's backwards, what we are actually saying is that rev for as plus bs is
--equal to rev of a's plus rev of bs. So if we add this what would happen?


--Now that we have this magic theorem what would happen. We the first thing we are
--going to do is make a theorem. The first thing we are going to do is make the
--list rev append 

--Line(102)


-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- (3.1)=========================================================================================================


--- Now we are moving on to another section and we will be working through using proofs a programs 


-- (3.1)=========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
-- =========================================================================================================
--
--No with a simple file I'm just going to introduce this on a simple program.

--Now we are just going to define some simple data types on some basic strings.
--AExp and expression and Val an int and Vname just a string. Now lets say that
--we want to encode some basic expressions.

type Val = int
type Vname  = String

data AExp
 = N Int
 | V Vname
 | Plus Aexp AExp
 deriving (Show)

--12
ex_12 = N 12

-- x + 0
ex_x_plus_9 = Plus ( V "x" ) (N 9)

-- x + ( y + z )
ex_x_plus_y_plus_z = Plus (V "x") (Plus (V "y") (V "z"))


--12
ex_12 = N 12

--Now by the way this is not a serious error

--now this is the last one line 169) So far so good?

--Next we want to be able to define the meaning of an expression. Meaning is a
--fancy word for value, what is the definition of ex_12, you can define this like
--a pervert, but that is up to you.

--Any reasonable person will allow this to evaluate to 12 unless you are some
--kind of pervert who has no regard for algebra


--Can we define what x + 0 is if we don't know the value of what x is? Now we need to define some mode of state


--We could just define it as a list of pairs, variables and their values. I'll
--start by saying that val is just equal to int. And so now I might try a function
--called a val. It takes a state and it returns a val.

--line 181)

--Now if I have plus of two expression A1 and A2, we must not forget the state
--because the state is also a parameter. (Answer from the audience) (Bugs, that
--Ranjit fixes).

--So all of this I've factored out into some sort of separate library called
--state. It's a little Haskell. It's general I don't want to restrict myself to
--strings. [link to the library]

--Now imagine that I have some statement x + y + z and some of these values do
--not have instantiated vales? Well we just give them a default values. Initially
--the values of all of the values is V. lets rename it to default.

--line 210)
--Now to continue in this abstract style I'm going to define two variables Set and
--Get. They are basic, the value of Set is subtle it says that it returns the
--value of state except that the value of key K's val is different in the state
--s'. It says that if the values of the key k is not equal to the key value that
--you passed in keep recusing, otherwise keep go in.

--Now if I look up the value of some other key, then I should get the original
--value. for any k0 and for any K if I update the value of any key k but i look
--up the value k', the I should get the original value that s had for  k. (If the
--value has not changed then return the old value prior to the other one being
--set.

--"Import state"

--add qualification. we can then call s.s.s

--now we will not have state, but a function called S.state. Who came first, the
--state or the value. Come on boss, what do you mean not in scope, that is what I
--mean as a matter of fact. Okay fantastic, Okay Sweet.

--Now lets make sure that we have evaluated things properly. Now if we define a
--world where every variable has the value one, then any value returned should
--have the value of 1.

type State = [(Vname, val)]

aval :: AExp -> State -> Val
aval (N k) = k
aval ()

--Q) what are v name and val (Audrey)

--A) answer Vnames are strings, and Vals are integers. These are just
--placeholders which could be arbitrary in the future


aval :: AExp -> State -> Val
aval (N k)  s = k
aval (V x)  s = lookup x s
aval (Plus a1 a2) s = (aval a1 s ) + (aval a2 s )

There is a file named State.HS where the values of states are defined
including a generic state which we can use for more general functions

--Stepping into this file
--
--Lets make up a state (reflect state one)

--Now what should it say, it should say that if we evaluate this monstrous
--expression. It should say ( why are you not working). If I evaluate, uuuuhh,
--what should I call this, EX. If I evaluate this in state 1. Now I'll call it foo.

{-@ reflect set @-}
set :: Gstate kv -. k -> v -> GState k v
set :: (Gstate kvs v0) k v = GState ((k,v) : kvs) v0


--There are a number of interesting properties which can be ascribed to this
--for instance if we set a variable, we should defiantly get it back

get_set :: k:_ -> v:_ -> s:_ -> P get ( set ( s k v ) k == v) 

-- ////////////////////////////////////
-- //back into the liquid haskell world
-- ////////////////////////////////////
-- x + ( y + z )
ex_x_plus_y_plus_z = Plus (V "x") (Plus (V "y") (V "z"))

{-@ foo :: {aval ex state1 == 3 } -@-}

{-@ reflect state1 @-}
state :: State
state 1 = init 1

type State = S.GState Vname Val

{-@ reflect aval @-}
aval :: AExp -> State -> Val
aval (N k)  s = k
aval (V x)  s = lookup x s
aval (Plus a1 a2) s = (aval a1 s ) + (aval a2 s )

-- NEXT CLASS

--we are going to work on the formulas used today and perform some optimizations
--on them. What does that mean? The state which is output by the non-optimized
--version is the same as those which are output by the optimized version

Plus a 0 ===> a

--In the next class we are going to also define a complier and we are going to
--check that the output of the compiler is also correct
