### CSE 230: Programming Languages
### Winter 2019
### Wednesday, March 13
##### Instructor: Ranjit Jhala
##### Scribe: Yufeng Gao, Linbin Yang

1. Recap Lecture 3.11:

  (1) Definition of Floyd-Hoare triple {P} c {Q} : If P is true in the initial state and command c finishes execution, then Q is true in the final state.

  (2) Rules:

    <1> Consequence Rule:

        {P} c {Q}, P' => P, Q => Q'
        ---------------------------
                {P'} c {Q'}

        For example:
        {x > 0} c {y == 10}, (x == 5) => (x > 0), (y == 10) => (y > 0)
        -------------------------------------------------------------- 
                              {x == 5} c {y > 0}

    <2> Empty Statement Rule (Rule of Skip): 
    
        ------------
        {P} SKip {P}

    <3> Rule of Composition (Rule of Sequencing):

        {B} c1 {Mid}, {Mid} c2 {Q}
        -------------------------- 
              {B} c1; c2 {Q}

    <4> Assignment Rule:
    
        -------------------
        {P[a/x]} x := a {P}

    <5> Conditional Rule:

            {P} c1 {Q}, {Q} c2 {Q}
        ----------------------------
        {P} if b then c1 else c2 {Q}


2. Revisit the conditional rule:

  In the last lecture, we mentioned that to prove {P} if b then c1 else c2 {Q} is a valid legit, we can prove {P} c1 {Q} and {P} c2 {Q}
  first, but the fact is sometimes you cannot prove both.

  For example, if we have a Floyd-Hoare triple like below:

    {x == 5}
    if x >= 0
      r = x
    else
      r = 0 - x
    {r >= 0}

  We can prove {P} c1 {Q}, which is {x == 5} r = x {r >= 0};
  But we cannot prove {P} c2 {Q}, which is {x == 5} r = 0 - x {r >= 0}.

  So instead, if we can prove {P} c1 {Q} under condition: b and {P} c2 {Q} under condition not b, we can be sure that our original Floyd-Hoare triple is a valid legit. 

  Thus we revise our conditional rule as below:

    {P ^ b} c1 {Q}, {P ^ (not b)} c2 {Q}
    ------------------------------------
        {P} if b then c1 else c2 {Q}

3. Now let's look at {P} while b do c {Q}:  

  Like the conditional rule, to prove this HF triple is legit, we have to 
  consider two situations:

  (1) b is false: 
      
      We break out of the loop and reach the state where P ^ not b is true, 
      thus we can prove that {P ^ (not b)} implies {Q} and use the consequence rule;

  (2) b is true: 
      
      Our problem becomes proving {P ^ b} c; while b do c {Q}, we can prove 
      this by proving there is a middle assertion Mid such that {P ^ b} c {Mid}
      and {Mid} while b do c {Q}. 

      If we can prove P is a loop invariant, that is, {P ^ b} c {P}, then we 
      can do induction on the true branch and finally reach situation (1) for the 
      false branch.

  To sum up, our proof tree is as below:

    {P ^ b} c {P}, {P ^ not b} => {Q}
    ---------------------------------
          {P} while b do c {Q} 

  The proof tree above is a combination of the while rule and the consequence 
  rule, we can extract the while rule out:

            {P ^ b} c {P}
    ------------------------------
    {P} while b do c {P ^ (not b)}

4. Let's discuss how to prove the validity of assertions:
  
  The validaty of an assertion is defined as:
    
    For all states, if assertion P is evaluated to true, P is a valid assertion.

  Examples: 
    (1) x >= 0 is not valid;
    (2) x >= 0 || x < 0 is valid;
    (3) (x <= 0) => (x - 1 <= 0) is valid; 
        *[Here '<=' is less than or equal to, '=>' is imply]

  Let's now look at how to prove the validity of an assertion using LH.
  
  First, We define a type Valid as:
    
    {-@ type Valid P = s:State -> { v: Proof | bval P s } @-}
    type Valid = State -> Proof 

  Then we define a function checkValid to check the validity of an assertion:

  \begin{code}
    {-@ checkValid :: p:_ -> Valid p -> () @-}
    checkValid :: Assertion -> Valid -> ()
    checkValid p v = ()

    ex0 :: checkValid e0 (\_ -> ())
      where 
        e0 = ((V "x") `Leq` (N 1))

    ex0_Imp_ex1 :: checkValid (e0 `bImp` e1) (\_ -> ())
      where
        e0 = ((V "x") `Leq` (N 1))
        e1 = ((V "x") `Minus` (N 1)) `Leq` (N 0)
  \end{code}

5. Now look at the Floyd-Hoare proof system:

  \begin{code}
  data FHP where 
    FH :: Assertion -> Com -> Assertion -> FHP

  data FH where 
    FHSkip    :: Assertion -> FH 
    FHAssign  :: Assertion -> Vname -> AExp -> FH 
    FHSeq     :: Assertion -> Com -> Assertion -> Com -> Assertion -> FH -> FH -> FH 
    FHIf      :: Assertion -> Assertion -> BExp -> Com -> Com -> FH -> FH -> FH
    FHWhile   :: Assertion -> BExp -> Com -> FH -> FH 
    FHConPre  :: Assertion -> Assertion -> Assertion -> Com -> Valid -> FH -> FH 
    FHConPost :: Assertion -> Assertion -> Assertion -> Com -> FH -> Valid -> FH 

  {-@ data FH where 
        FHSkip   :: p:_
                 -> Prop (FH p Skip p) 
      | FHAssign :: q:_ -> x:_ -> a:_
                 -> Prop (FH (bsubst x a q) (Assign x a) q) 
      | FHSeq    :: p:_ -> c1:_ -> q:_ -> c2:_ -> r:_ 
                 -> Prop (FH p c1 q) 
                 -> Prop (FH q c2 r) 
                 -> Prop (FH p (Seq c1 c2) r) 
      | FHIf     :: p:_ -> q:_ -> b:_ -> c1:_ -> c2:_
                 -> Prop (FH (bAnd p b)       c1 q) 
                 -> Prop (FH (bAnd p (Not b)) c2 q)
                 -> Prop (FH p (If b c1 c2) q)
      | FHWhile  :: p:_ -> b:_ -> c:_
                 -> Prop (FH (bAnd p b) c p) 
                 -> Prop (FH p (While b c) (bAnd p (Not b)))
      | FHConPre :: p':_ -> p:_ -> q:_ -> c:_  
                 -> Imply p' p
                 -> Prop (FH p c q) 
                 -> Prop (FH p' c q)
      | FHConPost :: p:_ -> q:_ -> q':_ -> c:_  
                  -> Prop (FH p c q) 
                  -> Imply q q'
                  -> Prop (FH p c q')
    @-}
    \end{code}

    \begin{code}
  --------------------------------------------------------------------------------
  -- | `Legit` formalizes the notion of when a Floyd-Hoare triple is legitimate 
  --------------------------------------------------------------------------------
  
  {-
    Note that we have already define Type Assertion = BStep
    The type Legit take three parameters:
    -P : Assertion, Pre-condition
    -C : Com, Command
    -Q : Assertion, Pos-Condition
    State s converted to s' after taking command C. P is true in s and Q is true in s'.
    This is the concept of legit.
  -}

  {-@ type Legit P C Q =  s:{State | bval P s} 
                       -> s':_ -> Prop (BStep C s s') 
                       -> {bval Q s'} 
    @-}
  type Legit = State -> State -> BStep -> Proof 
    \end{code}

  Problems:

  (1) How to prove the soundness of Floyd-Hoare Logic:

    \begin{code}
    {-@ thm_fh_legit :: p:_ -> c:_ -> q:_ -> Prop (FH p c q) -> Legit p c q @-}
    \end{code}

    This is one of the final problems. 
    *(Hint: divide into two sub parts and solve them separately.)
  
  (2) Is it possible to prove thm_Legit_fh?
    
    \begin{code}
    thm_fh_legit :: p:_ -> c:_ -> q:_ -> Legit p c q -> Prop (FH p c q) 
    \end{code}

    Yes.

    Example: {True} While True Skip {x >= 0} 
           * [This is always a valid legit]

    Analysis: 
     First prove {True} While True Skip {True ^ (not True)}, then apply the 
     consequence rule to prove the example FH triple, that is:

    First Step:

              {True ^ True} Skip {True}
      ------------------------------------------ While Rule
      {True} While True Skip {True ^ (not True)}

    Second Step:

      {True} While True Skip {True ^ (not True)}, {True ^ (not True)} => {x >= 0}
      --------------------------------------------------------------------------- Consequence Rule
                            {True} While True Skip {x >= 0}

6. Let's try to find the best pre-condition P for HF tripe {P} c {Q}
   given command c and assertion Q. 

  We formalize this problem as below:

  pre c Q = P 
  s.t. {P} c {Q} and if there is an assertion P' s.t. {P'} c {Q}, then P' => P

  Then let's look at several examples:

    (1) pre skip {Q} = Q

    (2) pre (c1;c2) {Q} = pre c1 (pre c2 Q)

    (3) pre (if b then c1 else c2) {Q} = (b => pre c1 Q) ^ (not b => pre c2 Q)

    (4) pre (while b do c) {Q} = b