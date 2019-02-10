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
