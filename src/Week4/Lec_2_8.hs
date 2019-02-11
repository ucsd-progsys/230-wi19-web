{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--diff"       @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Lec_2_8 where

import           Prelude hiding ((++)) 
import           ProofCombinators 
import           Lists 
import           Expressions 
import qualified State as S 


-----------------------------------------------------------------------
-- Relations
type Rel a = a -> a -> Bool

-- | The Prop describing the closure of a relation 

data PathP a where
  Path :: Rel a -> a -> a -> PathP a

-- | The Predicate describing the closure of a relation 
data Path a where
  Refl :: Rel a -> a -> Path a
  Step :: Rel a -> a -> a -> a -> Path a -> Path a

{-@ data Path a where
      Refl :: r:Rel a -> x:a -> Prop (Path r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Path r y z) -> Prop (Path r x z)
  @-}

--------------------------------------------------------------------------------

-- x -> ... -> y        y -> ... -> z 
--------------------------------------
-- x -> ... -> z



{-@ lemma_Path_trans :: r:Rel a -> x:a -> y:a -> z:a
      -> Prop (Path r x y)
      -> Prop (Path r y z)
      -> Prop (Path r x z)
  @-}
lemma_Path_trans :: Rel a -> a -> a -> a -> Path a -> Path a -> Path a
lemma_Path_trans r x y z (Refl mumble grumble) p_yz 
  = p_yz 

-- p_xy = x = x 
-- p_xy                        :: Prop (Path r      x       y)
-- p_xy == Refl mumble grumble :: Prop (Path mumble grumble grumble)

lemma_Path_trans r x y z (Step _r _x x1 _y p_x1y) p_yz 
  = p_xz 
  where 
    p_xz  = Step r x x1 z p_x1z                  -- x -> x1 -> ... -> z
    p_x1z = lemma_Path_trans r x1 y z p_x1y p_yz -- Prop (Path r x1 z)

-- p_xy = x -> x1 -> ... -> y
-- p_xy                        :: Prop (Path r x y)
-- p_xy == Step r x x1 y p_x1y :: Prop (Path r x y)
-- p_x1y                       :: Prop (Path r x1 y)
-- p_yz                        :: Prop (Path r y  z)

isPal :: (Eq a) => [a] -> Bool
isPal xs = xs == rev xs 


--------------------------------------------------------------------------------
-- | The Prop declaring the Palindrome predicate 
data PalP a where
  Pal :: [a] -> PalP a

-- | The Predicate implementing the Palindrom predicate 
data Pal a where
  Pal0 :: Pal a 
  Pal1 :: a -> Pal a 
  Pals :: a -> [a] -> Pal a -> Pal a 

{-@ data Pal a where
      Pal0 :: Prop (Pal []) 
    | Pal1 :: x:_ -> Prop (Pal (single x)) 
    | Pals :: x:_ -> xs:_ -> Prop (Pal xs) -> Prop (Pal (mkPal x xs)) 
  @-}

{-@ lemma_pal :: xs:_ -> p:Prop (Pal xs) -> { xs == rev xs } @-}
lemma_pal :: [a] -> Pal a -> Proof 
lemma_pal []  _ = () 
lemma_pal [x] _ = () 
lemma_pal xs  (Pal0 {}) = impossible "really"
lemma_pal xs  (Pal1 {}) = impossible "really"
lemma_pal xs  py@(Pals y ys pal_ys) 
  = rev xs 
  === rev (y : (ys ++ [y]))
  === rev (ys ++ [y]) ++ [y]
    ? lemma_rev_app ys [y]
  === (rev [y] ++ rev ys) ++ [y]
  ===  ([y] ++ rev ys) ++ [y]
    ? lemma_pal ys pal_ys 
  ===  ([y] ++ ys) ++ [y]
  === xs 
  *** QED 

-- py     :: Prop (Pal (mkPal y ys)) 
-- py     :: Prop (Pal xs)
-- xs     = y : (ys ++ [y])
-- pal_ys :: Prop (Pal ys) -- >by IH --> ys == rev ys

{-@ reflect single @-}
single :: a -> [a]
single x = [x]

{-@ reflect mkPal @-}
mkPal :: a -> [a] -> [a]
mkPal x xs = x : (xs ++ [x])

dummy :: Int
dummy = 10 


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{- 

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 

WANT: 


  (AVal s a n)

  - The expression `a` 
  - ... in the state `s` 
  - ... evaluates to the value `n`

Numbers 

      -------------------[AvalN]
        AVal s (N n) n

      --------------------------[AvalV]
        AVal s (V x) (get s x)

        (AVal s a1 n1) (AVal s a2 n2)
      ---------------------------------[AvalP]
        AVal s (Plus a1 a2) (n1 + n2) 
-}

-- | The Prop declaring the AVal predicate 
data AvalP where
  Aval :: State -> AExp -> Val -> AvalP 

-- | The Predicate implementing the Palindrom predicate 
data Aval where
  AvalN :: State -> Val   -> Aval 
  AvalV :: State -> Vname -> Aval 
  AvalP :: State -> AExp -> Val -> AExp -> Val -> Aval -> Aval -> Aval 

{-@ data Aval where
      AvalN :: s:_ -> n:_ 
            -> Prop (Aval s (N n) n) 
    | AvalV :: s:_ -> x:_ 
            -> Prop (Aval s (V x) (S.get s x)) 
    | AvalP :: s:_ -> a1:_ -> n1:_ -> a2:_ -> n2:_ 
            -> Prop (Aval s a1 n1) 
            -> Prop (Aval s a2 n2)
            -> Prop (Aval s (Plus a1 a2) {n1 + n2})
  @-}

{-@ lem_Aval :: s:_ -> a:_ -> n:_ -> Prop (Aval s a n) 
              -> { n == aval a s } @-}
lem_Aval :: State -> AExp -> Val -> Aval -> Proof 
lem_Aval s (N n)        _n (AvalN {}) 
   = () 
lem_Aval s (V x)        _  (AvalV {}) 
   = () 
lem_Aval s (Plus a1 a2) _  (AvalP _s _a1 n1 _a2 n2 p_a1_n1 p_a2_n2) 
   =   lem_Aval s a1 n1 p_a1_n1 -- aval a1 s == n1 
   &&& lem_Aval s a2 n2 p_a2_n2 -- aval a2 s == n2
lem_Aval s _ _ _      
   = impossible "hush, GHC." 

{-@ reflect add @-}
add :: Val -> Val -> Val
add x y = x + y
