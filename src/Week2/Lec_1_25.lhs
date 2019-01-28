\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection"  @-}

{-# LANGUAGE PartialTypeSignatures #-}

module Lec_1_25 where 

import Prelude hiding (sum)

import ProofCombinators

data Peano 
  = Z 
  | S Peano 
  deriving (Eq, Show)

{-@ reflect add @-}
add :: Peano -> Peano -> Peano  
add Z     m = m 
add (S n) m = S (add n m)

{-@ thm_Z_add :: p:Peano -> { add p Z == p } @-} 
thm_Z_add :: Peano -> Proof 

thm_Z_add Z     
    = add Z Z 
    === Z 
    *** QED 

thm_Z_add (S p) 
    = add (S p) Z 
    === S (add p Z) ? thm_Z_add p 
    === S p 
    *** QED 

-- forall x y, add x y == add y x

{-@ thm_add_com :: x:_ -> y:_ -> { add x y == add y x } @-}
thm_add_com :: Peano -> Peano -> Proof 
thm_add_com Z y 
  =   add Z y 
  === y 
      ? thm_Z_add y
  === add y Z 
  *** QED 

thm_add_com (S x') y 
  =   add (S x') y 
  === S (add x'  y)
      ? thm_add_com x' y
  === S (add y x')
    ? lemma y x'
  === add y (S x') 
  *** QED

{-@ lemma :: apple:_ -> banana:_ 
          -> { add apple (S banana) == S (add apple banana) } 
  @-}
lemma :: Peano -> Peano -> Proof 
lemma Z      b 
  = add Z (S b) 
  === S b 
  === S (add Z b) 
  *** QED 

lemma (S a') b 
  =   add (S a') (S b) 
  === S (add a' (S b))
    ? lemma a' b        
  === S (S (add a' b))
  === S (add (S a') b) 
  *** QED 
  
-- thm_add_comm 

--------------------------------------------------------------------------------
data List a = Nil | Cons a (List a)
  deriving (Eq, Show)

{-@ reflect app @-}
app :: List a -> List a -> List a 
app Nil         ys = ys 
app (Cons x xs) ys = Cons x (app xs ys)

{-@ ex_list :: () -> {app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) == Cons 1 (Cons 2 (Cons 3 Nil)) } @-}
ex_list :: () -> Proof 
ex_list _ 
  =   app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) 
  === Cons 1 (app Nil ((Cons 2 (Cons 3 Nil))))
  === Cons 1 (Cons 2 (Cons 3 Nil)) 
  *** QED

{-@ thm_app_nil :: l:_ -> { app l Nil == l } @-}
thm_app_nil :: List a -> Proof 
thm_app_nil Nil        
  = app Nil Nil === Nil *** QED 

thm_app_nil (Cons h t) 
  =   app (Cons h t) Nil 
  === Cons h (app t Nil)
    ? thm_app_nil t
  === Cons h t 
  *** QED 
 
{-@ thm_app_assoc :: l1:_ -> l2:_ ->l3:_ -> { app (app l1 l2) l3 == app l1 (app l2 l3) } @-}
thm_app_assoc :: List a -> List a -> List a -> Proof 
thm_app_assoc Nil ys zs 
  =   app (app Nil ys) zs 
  === app ys zs
  === app Nil (app ys zs) 
  *** QED 

thm_app_assoc (Cons x xs) ys zs 
  =   app (app (Cons x xs) ys) zs 
  === app (Cons x (app xs ys)) zs 
  === Cons x (app (app xs ys) zs)
    ? thm_app_assoc xs ys zs
  === Cons x (app xs (app ys zs))
  === app (Cons x xs) (app ys zs) 
  *** QED 



-- thm_append_assoc 

-- rev 

-- thm_rev_rev

\end{code}




