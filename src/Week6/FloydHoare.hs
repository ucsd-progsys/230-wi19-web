{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
{-@ infixr ++              @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr <~              @-}  -- TODO: Silly to have to rewrite this annotation!

-- | Inspired by http://flint.cs.yale.edu/cs428/coq/sf/Hoare.html 

{-# LANGUAGE GADTs #-}

module FloydHoare where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
import           Expressions  
import           Imp 
import           BigStep hiding (And)


--------------------------------------------------------------------------------
{- | A Floyd-Hoare triple is of the form 

        { P }  c { Q }

     where 
      
     - `P` and `Q` are assertions (think `BExp`) and 
     - `c` is a command (think `Com`) 
    
     A Floyd-Hoare triple states that 

     IF 

     * The program `c` is starts at a state where the *precondition* `P` is True, and 
     * The program finishes execution

     THEN 

     * At the final state, the *postcondition* `Q` will also evaluate to True.

     -}

{- | Lets paraphrase the following Hoare triples in English.

   1) {True}   c {X = 5}

   2) {X = m}  c {X = m + 5}

   3) {X <= Y} c {Y <= X}

   4) {True}   c {False}

-}


--------------------------------------------------------------------------------
-- | The type `Assertion` formalizes the type for the 
--   assertions (i.e. pre- and post-conditions) `P`, `Q`
--   appearing in the triples {P} c {Q}

type Assertion = BExp 
--------------------------------------------------------------------------------

{- 
--------------------------------------------------------------------------------
-- | The type `Triple` formalizes the notion of a "Floyd-Hoare Triple"
--------------------------------------------------------------------------------

data Triple = Triple 
  Assertion     -- ^ Precondition (assertion on starting state)
  Com           -- ^ Imp Command    
  Assertion     -- ^ Postcondition  (assertion on final state)
 
{-@ measure pre @-}
pre :: Triple -> Assertion
pre (Triple p _ _) = p 

{-@ measure post @-}
post :: Triple -> Assertion
post (Triple _ _ q) = q 

{-@ measure com @-}
com :: Triple -> Com 
com (Triple _ c _) = c 

{-@ type Legit T = s : {State | bval (pre T) s} 
                 -> s': _ 
                 -> Prop (BStep (com T) s s') 
                 -> {bval (post T) s'}  
  @-}
type Legit = State -> State -> BStep -> Proof 

{-@ leg1 :: Legit tr1 @-}


--------------------------------------------------------------------------------
-- | Example: {True}  X <~ 5  {X = 5} 
--------------------------------------------------------------------------------
{-@ reflect tr1 @-} 
tr1 :: Triple
tr1 = Triple
  tt 
    ("x" <~ N 5) 
  ((V "x") .==. (N 5)) 

--------------------------------------------------------------------------------
-- | Example: {True}  X <~ 5; y <- X  {X = 5} 
--------------------------------------------------------------------------------

{-@ reflect tr3 @-} 
tr3 :: Triple
tr3 = Triple
  tt 
    (("x" <~ N 5) @@ 
     ("y" <~ V "x"))
  ((V "y") .==. (N 5)) 

--------------------------------------------------------------------------------
-- | Example: {X = 2 && X = 3}  X <~ 5  {X = 0}
--------------------------------------------------------------------------------

{-@ reflect tr5 @-} 
tr5 :: Triple
tr5 = Triple
  (((V "x") .==. (N 2)) .&&. ((V "x") .==. (N 3))) 
    (("x" <~ N 5) @@ 
     ("y" <~ V "x"))
  ((V "x") .==. (N 0)) 

-} 
--------------------------------------------------------------------------------
{- | Legitimate Triples 
--------------------------------------------------------------------------------

Which of the following triples are "legit" i.e.,  the claimed relation between 
`pre`condition` `P`, `com`mand `C`, and `post`condition `Q` is true?

   1) {True}  
        X <~ 5 
      {X = 5}

   2) {X = 2} 
        X <~ X + 1 
      {X = 3}

   3) {True}  
        X <~ 5; 
        Y <~ 0 
      {X = 5}

   4) {True}  
        X <~ 5; 
        Y <~ X 
      {Y = 5}

   5) {X = 2 && X = 3} 
        X <~ 5 
      {X = 0}

   6) {True} 
        SKIP 
      {False}

   7) {False} 
        SKIP 
      {True}

   8) {True} 
        WHILE True DO 
          SKIP 
      {False}

   9) {X = 0}
        WHILE X <= 0 DO 
          X <~ X + 1 
      {X = 1}

   10) {X = 1}
         WHILE not (X <= 0) DO 
           X <~ X + 1 
       {X = 100}
 -}

--------------------------------------------------------------------------------
-- | `Legit` formalizes the notion of when a Floyd-Hoare triple is legitimate 
--------------------------------------------------------------------------------
{-@ type Legit P C Q = s:{State | bval P s} -> s':_ -> Prop (BStep C s s') -> {bval Q s'} @-}
type Legit = State -> State -> BStep -> Proof 

-- | {True}  X <~ 5  {X = 5} ---------------------------------------------------

{-@ leg1 :: Legit tt (Assign {"x"} (N 5)) (Equal (V {"x"}) (N 5)) @-}
leg1 :: Legit  
leg1 s s' (BAssign {}) 
  = S.lemma_get_set "x" 5 s 


-- | {True}  X <~ 5; y <- X  {X = 5} -------------------------------------------

{-@ leg3 :: Legit tt (Seq (Assign {"x"} (N 5)) (Assign {"y"} (V {"x"}))) (Equal (V {"y"}) (N 5)) @-}
leg3 :: Legit  
leg3 s s' (BSeq _ _ _ smid _ (BAssign {}) (BAssign {})) 
  = S.lemma_get_set "x" 5 s &&& S.lemma_get_set "y" 5 smid 


-- | {False}  X <~ 5  {X = 0} --------------------------------------------------

{-@ leg5 :: Legit ff (Assign {"x"} (N 5)) (Equal (V {"x"}) (N 22)) @-}
leg5 :: Legit  
leg5 s s' _ = () 


--------------------------------------------------------------------------------
-- | Two simple facts about Floyd-Hoare Triples --------------------------------
--------------------------------------------------------------------------------

{-@ lem_post_true :: p:_ -> c:_ -> Legit p c tt @-}
lem_post_true :: Assertion -> Com -> Legit
lem_post_true p c = \s s' c_s_s' -> () 

{-@ lem_pre_false :: c:_ -> q:_ -> Legit ff c q @-}
lem_pre_false :: Com -> Assertion -> Legit 
lem_pre_false c q = \s s' c_s_s' -> () 


-- | Assignment 

--  { Y = 1     }  X <~ Y      { X = 1 }

--  { X + Y = 1 }  X <~ X + Y  { X = 1 }

--  { a = 1     }  X <~ a      { X = 1 }


{- | Lets fill in the blanks

     { ??? } 
        x <~ 3 
     { x == 3 }

     { ??? } 
        x <~ x + 1 
     { x <= 5 }

     { ??? }
        x <~ y + 1 
     { 0 <= x && x <= 5 }

 -} 


{- | To conclude that an arbitrary postcondition `Q` holds after 
     `x <~ a`, we need to assume that Q holds before `x <~ a` 
     but with all occurrences of `x` replaced by `a` in `Q` 

     Lets revisit the example above:

     { ??? } 
        x <~ 3 
     { x == 3 }

     { ??? } 
        x <~ x + 1 
     { x <= 5 }

     { ??? }
        x <~ y + 1 
     { 0 <= x && x <= 5 }

  -} 

--------------------------------------------------------------------------------
-- | Skip 
--------------------------------------------------------------------------------
{-@ lem_skip :: p:_ -> (Legit p Skip p) @-}
lem_skip :: Assertion -> Legit 
lem_skip p = \s s' (BSkip {}) -> () 

--------------------------------------------------------------------------------
-- | Assignment
--------------------------------------------------------------------------------
{-@ lem_asgn :: x:_ -> a:_ -> q:_ -> 
      Legit (bsubst x a q) (Assign x a) q 
  @-}
lem_asgn :: Vname -> AExp -> Assertion -> Legit 
lem_asgn x a q = \s s' (BAssign {}) -> lem_bsubst x a q s

--------------------------------------------------------------------------------
-- | Sequencing 
--------------------------------------------------------------------------------
{-@ lem_seq :: c1:_ -> c2:_ -> p:_ -> q:_ -> r:_ 
            -> Legit p c1 q -> Legit q c2 r 
            -> Legit p (Seq c1 c2) r 
  @-}
lem_seq :: Com -> Com -> Assertion -> Assertion -> Assertion -> Legit -> Legit -> Legit 
lem_seq c1 c2 p q r l1 l2 = \s s' (BSeq _ _ _ smid _ t1 t2) -> 
  l1 s smid t1 &&& l2 smid s' t2 


--------------------------------------------------------------------------------
-- | Branches 
--------------------------------------------------------------------------------
{-@ lem_if :: b:_ -> c1:_ -> c2:_ -> p:_ -> q:_ 
           -> Legit (bAnd p b)       c1 q 
           -> Legit (bAnd p (Not b)) c2 q 
           -> Legit p (If b c1 c2)  q
  @-}
lem_if :: BExp -> Com -> Com -> Assertion -> Assertion -> Legit -> Legit -> Legit
lem_if b c1 c2 p q l1 l2 = \s s' bs -> case bs of 
  BIfF _ _ _ _ _ c2_s_s' -> l2 s s' c2_s_s'
  BIfT _ _ _ _ _ c1_s_s' -> l1 s s' c1_s_s'

--------------------------------------------------------------------------------
-- | Loops 
--------------------------------------------------------------------------------
{-@ lem_while :: b:_ -> c:_ -> p:_ 
              -> Legit (bAnd p b) c p 
              -> Legit p (While b c) (bAnd p (Not b)) 
  @-}
lem_while :: BExp -> Com -> Assertion -> Legit -> Legit 
lem_while b c p lbody = \s s' bs -> case bs of 
  BWhileF {} -> undefined 
  BWhileT {} -> undefined 

--------------------------------------------------------------------------------
-- | Consequence
--------------------------------------------------------------------------------
{-@ lem_conseq_pre :: p':_ -> p:_ -> q:_ -> c:_ 
                   -> Imply p' p -> Legit p c q 
                   -> Legit p' c q
  @-}
lem_conseq_pre :: Assertion -> Assertion -> Assertion -> Com -> Valid -> Legit -> Legit 
lem_conseq_pre p' p q c impl pcq = \s s' c_s_s' -> pcq (s ? (impl s)) s' c_s_s'

{-@ lem_conseq_post :: p:_ -> q:_ -> q':_ -> c:_ 
                    -> Legit p c q -> Imply q q' 
                    -> Legit p c q'
  @-}
lem_conseq_post :: Assertion -> Assertion -> Assertion -> Com -> Legit -> Valid -> Legit 
lem_conseq_post p q q' c pcq impl = \s s' c_s_s' -> pcq s s' c_s_s' ? (impl s') 


--------------------------------------------------------------------------------
-- | `Valid`ity of an assertion
--------------------------------------------------------------------------------

{-@ type Valid P = s:State -> { v: Proof | bval P s } @-}
type Valid = State -> Proof 

{-@ type Imply P Q = Valid (bImp P Q) @-}

{-@ v1 :: _ -> Imply (Leq (N 10) (V {"x"})) (Leq (N 5) (V {"x"})) @-} 
v1 :: a -> Valid 
v1 _ = \_ -> ()


{- 
{-@ v2 :: Valid p2 @-}
v2 :: Valid 
v2 = \_ -> ()

-- (0 < x && 0 < y) ===> (0 < x + y)
{-@ reflect p2 @-}
p2 = ((N 0) `Less` (V "x")) `bAnd` ((N 0) `Less` (V "y")) 
       `bImp` ((N 0) `Less` (Plus (V "x") (V "y")))
       
P => P'   {P'} c {Q'}     Q' => Q
------------------------------------
          {P}  c {Q}

data FHP where 
  FH :: Assertion -> Com -> Assertion -> FHP

data FH where 
  FHSkip   :: Assertion -> FH 
  FHAssign :: Assertion -> Vname -> AExp -> FH 
  FHSeq    :: Assertion -> Com -> Assertion -> Com -> Assertion -> FH -> FH -> FH 
  FHIf     :: Assertion -> Assertion -> BExp -> Com -> Com -> FH -> FH -> FH
  FHWhile  :: Assertion -> BExp -> Com -> FH -> FH 
  FHConseq :: Assertion -> Assertion -> Assertion -> Assertion -> Com -> FH -> FH 

{-@ data FH where 
      FHSkip   :: p:Assertion 
               -> Prop (FH p Skip p) 
    | FHAssign :: q:Assertion -> x:Vname -> a:AExp 
               -> Prop (FH (subst q x a) (Assign x a) q) 
    | FHSeq    :: p:Assertion -> c1:Com -> q:Assertion -> c2:Com -> r:Assertion 
               -> Prop (FH p c1 q) -> Prop (FH q c2 r) 
               -> Prop (FH p (Seq c1 c2) r) 
    | FHIf     :: p:Assertion -> q:Assertion -> b:BExp -> c1:Com -> c2:Com 
               -> Prop (FH (And p b)        c1 q) 
               -> Prop (FH (And p (Not b))) c2 q)
               -> Prop (FH p (If b c1 c2) q)
    | FHWhile  :: p:Assertion -> b:BExp -> c:Com
               -> Prop (FH (And p b) c p) 
               -> Prop (FH p (While b c) (And p (Not b)))
    | FHConseq :: p:Assertion -> p':{Assertion | implies p p'} -> q':Assertion -> q:{Assertion | implies q' q} -> c:Com
               -> Prop (FH p' c q') 
               -> Prop (FH p  c q)
  @-}

-}