{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--diff"       @-}
{-@ LIQUID "--ple-local"  @-}

module Language.ConcreteLH.Chapters.Ch02 where 

import Prelude hiding (map)
import Language.ConcreteLH.Lib.ProofCombinators

--------------------------------------------------------------------------------
-- | Section 2.2.2 
--------------------------------------------------------------------------------
data Peano = Z | S Peano 
  deriving (Eq, Show)

{-@ reflect add @-}
add         :: Peano -> Peano -> Peano 
add Z     m = m 
add (S n) m = S (add n m)

{-@ lemma_add_02 :: n:_ -> { add n Z = n } @-}
lemma_add_02 :: Peano -> Proof
lemma_add_02 Z     
  =   add Z Z 
  === Z 
  *** QED 

lemma_add_02 (S n) 
  =   add (S n) Z 
  === S (add n Z)
    ? lemma_add_02 n  
  === S n 
  *** QED 

--------------------------------------------------------------------------------
-- | Section 2.2.3 
--------------------------------------------------------------------------------

data List a = Nil | Cons a (List a)
  deriving (Eq, Show)

{-@ reflect app @-}
app :: List a -> List a -> List a 
app Nil ys         = ys 
app (Cons x xs) ys = Cons x (app xs ys)

{-@ reflect rev @-}
rev :: List a -> List a 
rev Nil         = Nil 
rev (Cons x xs) = app (rev xs) (Cons x Nil)

{-@ lemma_app_assoc :: xs:_ -> ys:_ -> zs:_ 
      -> { app (app xs ys) zs = app xs (app ys zs) } @-} 
lemma_app_assoc :: List a -> List a -> List a -> Proof 
lemma_app_assoc Nil ys zs 
  =   app (app Nil ys) zs 
  === app ys zs
  === app Nil (app ys zs)
  *** QED 

lemma_app_assoc (Cons x xs) ys zs 
  =   app (app (Cons x xs) ys) zs 
  === app (Cons x (app xs ys)) zs 
  === Cons x (app (app xs ys) zs) 
    ? lemma_app_assoc xs ys zs
  === Cons x (app xs (app ys zs))
  === app (Cons x xs) (app ys zs)
  *** QED 

{-@ lemma_rev_app :: xs:_ -> ys:_ -> { rev (app xs ys) = app (rev ys) (rev xs)} @-}
lemma_rev_app :: List a -> List a -> Proof 
lemma_rev_app Nil ys 
  =   rev (app Nil ys) 
  === rev ys
    ? lemma_app_Nil2 (rev ys)
  === app (rev ys) (rev Nil) 
  *** QED 

lemma_rev_app (Cons x xs) ys 
  =   rev (app (Cons x xs) ys)
  === rev (Cons x (app xs ys))
  === app (rev (app xs ys)) (Cons x Nil)
    ? lemma_rev_app xs ys 
  === app (app (rev ys) (rev xs)) (Cons x Nil)
    ? lemma_app_assoc (rev ys) (rev xs) (Cons x Nil)
  === app (rev ys) (app (rev xs) (Cons x Nil))
  === app (rev ys) (rev (Cons x xs))
  *** QED  
 

{-@ lemma_app_Nil2 :: xs:_ -> { app xs Nil = xs } @-}
lemma_app_Nil2 :: List a -> Proof 
lemma_app_Nil2 Nil 
  =   app Nil Nil 
  === Nil 
  *** QED 

lemma_app_Nil2 (Cons x xs) 
  =   app (Cons x xs) Nil 
  === Cons x (app xs Nil) 
    ? lemma_app_Nil2 xs 
  === Cons x xs 
  *** QED 


{-@ theorem_rev_rev :: xs:_ -> { rev (rev xs) = xs } @-}
theorem_rev_rev :: List a -> Proof 
theorem_rev_rev Nil 
  =   rev (rev Nil) 
  === Nil 
  *** QED 

theorem_rev_rev (Cons x xs) 
  =   rev (rev (Cons x xs)) 
  === rev (app (rev xs) (Cons x Nil)) 
    ? lemma_rev_app (rev xs) (Cons x Nil)
  === app (rev (Cons x Nil)) (rev (rev xs)) 
    ? theorem_rev_rev xs 
  === app (rev (Cons x Nil))           xs 
  === app (app (rev Nil) (Cons x Nil)) xs 
  === app (Cons x Nil)                 xs
  === Cons x (app Nil xs)
  === Cons x xs 
  *** QED 

--------------------------------------------------------------------------------
-- | Exercise 2.2 TODO 
--------------------------------------------------------------------------------
-- lemma_add_assoc 
-- lemma_add_comm 
-- double 
-- lemma_double_add 

--------------------------------------------------------------------------------
-- | Exercise 2.5 TODO
--------------------------------------------------------------------------------
-- sum_to :: n:Nat -> Nat 
-- lemma_sum_to :: n:_ -> { 2 * sum_to n = n * (n - 1) } 


--------------------------------------------------------------------------------
-- | Section 2.3
--------------------------------------------------------------------------------
data Tree a = Tip | Node (Tree a) a (Tree a)
  deriving (Show)

{-@ reflect mirror @-}
mirror :: Tree a -> Tree a 
mirror Tip          = Tip 
mirror (Node l a r) = Node (mirror r) a (mirror l)

{-@ lemma_mirror :: t:_ -> { mirror (mirror t) = t } @-}
lemma_mirror :: Tree a -> Proof 
lemma_mirror Tip 
  =   mirror (mirror Tip) 
  === Tip 
  *** QED

lemma_mirror (Node l a r) 
  =   mirror (mirror (Node l a r))
  === mirror (Node (mirror r) a (mirror l))
  === Node (mirror (mirror l)) a (mirror (mirror r))
    ? lemma_mirror l &&& lemma_mirror r
  === Node l a r 
  *** QED
 
--------------------------------------------------------------------------------
-- | Exercise 2.6 
--------------------------------------------------------------------------------

{-@ reflect sum_tree @-}
sum_tree :: Tree Int -> Int 
sum_tree Tip           = 0 
sum_tree (Node l a r)  = sum_tree l + a + sum_tree r 

{-@ reflect sum_list @-}
sum_list :: List Int -> Int 
sum_list Nil         = 0 
sum_list (Cons x xs) = x + sum_list xs 


{-@ reflect contents @-}
contents :: Tree a -> List a 
contents Tip          = Nil 
contents (Node l a r) = Cons a (app (contents l) (contents r))

{-@ ple lemma_sum_app @-}
{-@ lemma_sum_app :: xs:_ -> ys:_ -> 
      { sum_list (app xs ys) = sum_list xs + sum_list ys } @-}
lemma_sum_app :: List Int -> List Int -> Proof 
lemma_sum_app Nil ys         =  trivial 
lemma_sum_app (Cons x xs) ys = lemma_sum_app xs ys

{-@ lemma_sum_contents :: t:_ -> { sum_tree t = sum_list (contents t) } @-}
lemma_sum_contents :: Tree Int -> Proof 
lemma_sum_contents Tip 
  =   sum_tree Tip 
  === sum_list (contents Tip) 
  *** QED 

lemma_sum_contents (Node l a r) 
  =   sum_tree (Node l a r)
  === sum_tree l + a + sum_tree r 
    ? lemma_sum_app (contents l) (contents r) &&& lemma_sum_contents l &&& lemma_sum_contents r
  ===  a + sum_list (app (contents l) (contents r))
  === sum_list (Cons a (app (contents l) (contents r)))
  === sum_list (contents (Node l a r))
  *** QED
   
  
--------------------------------------------------------------------------------
-- | Exercise 2.8
--------------------------------------------------------------------------------
{-@ reflect intersperse @-}
intersperse :: a -> List a -> List a 
intersperse _ Nil          = Nil 
intersperse a (Cons x Nil) = Cons x Nil 
intersperse a (Cons x xs)  = Cons x (Cons a (intersperse a xs)) 

{-@ reflect map @-}
map :: (a -> b) -> List a -> List b 
map _ Nil         = Nil 
map f (Cons x xs) = Cons (f x) (map f xs)

{-@ ple lemma_map_intersperse  @-}
{-@ lemma_map_intersperse :: f:_ -> x:_ -> ys:_ -> 
      { map f (intersperse x ys) = intersperse (f x) (map f ys) } @-}
lemma_map_intersperse :: (a -> b) -> a -> List a -> Proof 
lemma_map_intersperse _ _ Nil          =  () 
lemma_map_intersperse _ _ (Cons _ Nil) =  () 
lemma_map_intersperse f x (Cons _ ys)  =  lemma_map_intersperse f x ys 

{-@ lemma_map_intersperse' :: f:_ -> x:_ -> ys:_ -> 
      { map f (intersperse x ys) = intersperse (f x) (map f ys) } @-}
lemma_map_intersperse' :: (a -> b) -> a -> List a -> Proof 
lemma_map_intersperse' f x Nil          
  =   map f (intersperse x Nil)
  === intersperse (f x) (map f Nil)
  *** QED

lemma_map_intersperse' f x (Cons y Nil) 
  =   map f (intersperse x (Cons y Nil))
  === Cons (f y) (map f Nil)
  === intersperse (f x) (map f (Cons y Nil))
  *** QED

lemma_map_intersperse' f x (Cons y ys)  
  =   map f (intersperse x (Cons y ys))
  === map f (Cons y (Cons x (intersperse x ys)))
  === Cons (f y) (map f (Cons x (intersperse x ys)))
  === Cons (f y) (Cons (f x) (map f (intersperse x ys)))
    ? lemma_map_intersperse' f x ys
  === intersperse (f x) (Cons (f y) (map f ys))
  === intersperse (f x) (map f (Cons y ys))
  *** QED

--------------------------------------------------------------------------------
-- | Section 2.4
--------------------------------------------------------------------------------

{-@ reflect itrev @-}
itrev :: List a -> List a -> List a 
itrev Nil         ys = ys 
itrev (Cons x xs) ys = itrev xs (Cons x ys)

{-@ lemma_itrev :: xs:_ -> ys:_ -> { itrev xs ys = app (rev xs) ys } @-}
lemma_itrev :: List a -> List a -> Proof 
lemma_itrev Nil ys     
  =   itrev Nil ys 
  === ys 
  === app (rev Nil) ys  
  *** QED 

lemma_itrev (Cons x xs) ys 
  =   itrev (Cons x xs) ys 
  === itrev xs (Cons x ys) 
    ? lemma_itrev xs (Cons x ys)
  === app (rev xs) (Cons x ys)
  === app (rev xs) (Cons x (app Nil ys)) 
  === app (rev xs) (app (Cons x Nil)  ys) 
    ? lemma_app_assoc (rev xs) (Cons x Nil) ys
  === app (app (rev xs) (Cons x Nil)) ys
  === app (rev (Cons x xs)) ys
  *** QED



--------------------------------------------------------------------------------
-- | Exercise 2.9
--------------------------------------------------------------------------------
{-@ reflect itadd @-}
itadd :: Peano -> Peano -> Peano 
itadd Z     m = m 
itadd (S n) m = itadd n (S m)

{- ple lemma_itadd @-}
{-@ lemma_itadd :: n:_ -> m:_ -> {itadd n m = add n m} @-}
lemma_itadd :: Peano -> Peano -> Proof 
lemma_itadd Z     m 
  = itadd Z m 
  === m 
  === add Z m 
  *** QED 

lemma_itadd (S n) m 
  =   itadd (S n) m 
  === itadd n (S m) 
    ? lemma_itadd n (S m) 
  === add n (S m) 
    ? lemma_add_r n m 
  === add (S n) m 
  *** QED 

{-@ ple lemma_add_r @-}
{-@ lemma_add_r :: n:_ -> m:_ -> { add (S n) m = add n (S m) } @-}
lemma_add_r :: Peano -> Peano -> Proof 
lemma_add_r Z     _ = () 
lemma_add_r (S n) m = lemma_add_r n m 

--------------------------------------------------------------------------------
-- | Exercise 2.10
--------------------------------------------------------------------------------
data Tree0 = Tip0 | Node0 Tree0 Tree0 
  deriving (Show)

{-@ reflect size0 @-}
size0 :: Tree0 -> Int 
size0 Tip0        = 1 
size0 (Node0 l r) = size0 l + size0 r  

{-@ reflect explode @-}
{-@ explode :: Nat -> Tree0 -> Tree0 @-}
explode :: Int -> Tree0 -> Tree0
explode 0 t = t 
explode n t = explode (n-1) (Node0 t t)

{-@ reflect pow @-}
{-@ pow :: Nat -> n:Nat -> Nat / [n] @-}
pow :: Int -> Int -> Int
pow k 0 = 1 
pow k n = k * pow k (n - 1) 

{-@ lemma_explode_size :: n:Nat -> t:_ -> { size0 (explode n t) = pow 2 n * size0 t } @-}
lemma_explode_size :: Int -> Tree0 -> Proof 
lemma_explode_size 0 t 
  =   size0 (explode 0 t) 
  === size0 t 
  === pow 2 0 * size0 t 
  *** QED 

lemma_explode_size n t 
  =   size0 (explode n t) 
  === size0 (explode (n-1) (Node0 t t)) 
    ? lemma_explode_size (n-1) (Node0 t t)
  === pow 2 (n-1) * size0 (Node0 t t)
  === pow 2 (n-1) * 2 * size0 t 
  === pow 2 n * size0 t 
  *** QED 

-- Whoa, PLE!
{-@ ple lemma_explode_size' @-}
{-@ lemma_explode_size' :: n:Nat -> t:_ -> { size0 (explode n t) = pow 2 n * size0 t } @-}
lemma_explode_size' :: Int -> Tree0 -> Proof 
lemma_explode_size' 0 t = () 
lemma_explode_size' n t = lemma_explode_size' (n-1) (Node0 t t)

{- 
explode 1 t = (Node0 t t)
explode 2 t = Node0 (Node0 t t) (Node0 t t)
explode 3 t = Node0 (Node0 (Node0 t t) (Node0 t t)) (Node0 (Node0 t t) (Node0 t t)) 

size (explode n t) =  pow 2 n * size t
2^3 
-}

--------------------------------------------------------------------------------
-- | Exercise 2.11
--------------------------------------------------------------------------------

data Exp 
  = Var 
  | Con Int 
  | Add Exp Exp 
  | Mul Exp Exp
  deriving (Show)

{-@ reflect eval @-}
eval :: Exp -> Int -> Int 
eval Var         x = x 
eval (Con n)     _ = n 
eval (Add e1 e2) x = eval e1 x + eval e2 x 
eval (Mul e1 e2) x = eval e1 x * eval e2 x 

type Poly = List Int

{-@ reflect evalp @-}
evalp :: Poly -> Int -> Int 
evalp Nil         _ = 0 
evalp (Cons c cs) x = c + x * (evalp cs x) 

{-@ reflect addPoly @-}
addPoly :: Poly -> Poly -> Poly 
addPoly Nil         p             = p 
addPoly p           Nil           = p 
addPoly (Cons c1 p1) (Cons c2 p2) = Cons (c1 + c2) (addPoly p1 p2) 

{-@ ple lemma_add_poly @-}
{-@ lemma_add_poly :: p1:_ -> p2:_ -> x:_ -> 
      { evalp (addPoly p1 p2) x = evalp p1 x + evalp p2 x } @-}
lemma_add_poly :: Poly -> Poly -> Int -> Proof 
lemma_add_poly Nil          p          _ = () 
lemma_add_poly p            Nil        _ = () 
lemma_add_poly (Cons _ p1) (Cons _ p2) x = lemma_add_poly p1 p2 x 

{-@ reflect mulConst @-}
mulConst :: Int -> Poly -> Poly 
mulConst c Nil         = Nil 
mulConst c (Cons d ds) = Cons (c * d) (mulConst c ds)

{-@ reflect mulPoly @-}
mulPoly :: Poly -> Poly -> Poly 
mulPoly Nil         _ = Nil
mulPoly (Cons c cs) p = addPoly (mulConst c p) (Cons 0 (mulPoly cs p)) 

{-@ ple lemma_mul_const @-}
{-@ lemma_mul_const :: c:_ -> p:_ -> x:_ -> 
     { evalp (mulConst c p) x = c * evalp p x } @-}
lemma_mul_const :: Int -> Poly -> Int -> Proof 
lemma_mul_const _ Nil _        = ()
lemma_mul_const c (Cons _ p) x = lemma_mul_const c p x

{-@ ple lemma_mul_poly @-}
{-@ lemma_mul_poly :: p1:_ -> p2:_ -> x:_ -> 
      { evalp (mulPoly p1 p2) x = evalp p1 x * evalp p2 x } @-}
lemma_mul_poly :: Poly -> Poly -> Int -> Proof 
lemma_mul_poly Nil         _ _ = ()
lemma_mul_poly (Cons c cs) p x = lemma_add_poly (mulConst c p) (Cons 0 (mulPoly cs p)) x
                             &&& lemma_mul_const c p x 
                             &&& lemma_mul_poly cs p x 
{- 
lemma_mul_poly Nil         _ _ 
  = () 
lemma_mul_poly (Cons c cs) p x 
  =   evalp (mulPoly (Cons c cs) p) x 
  === evalp (addPoly (mulConst c p) (Cons 0 (mulPoly cs p))) x 
    ? lemma_add_poly (mulConst c p) (Cons 0 (mulPoly cs p)) x
  === evalp (mulConst c p) x + evalp (Cons 0 (mulPoly cs p)) x 
    ? lemma_mul_const c p x 
  === (c * (evalp p x))      + evalp (Cons 0 (mulPoly cs p)) x
  === (c * (evalp p x))      + 0 + x * (evalp (mulPoly cs p) x)
    ? lemma_mul_poly cs p x 
  === (c * (evalp p x))      + x * (evalp cs x * evalp p x) 
  === (c + x * (evalp cs x)) * (evalp p x)
  === (evalp (Cons c cs) x)  * (evalp p x)
  *** QED  
-}

{-@ reflect coeffs @-}
coeffs :: Exp -> Poly 
coeffs Var         = Cons 0 (Cons 1 Nil) 
coeffs (Con i)     = Cons i Nil   
coeffs (Add e1 e2) = addPoly (coeffs e1) (coeffs e2)
coeffs (Mul e1 e2) = mulPoly (coeffs e1) (coeffs e2)

{-@ ple lemma_coeffs @-}
{-@ lemma_coeffs :: e:_ -> x:_ -> {evalp (coeffs e) x = eval e x} @-}
lemma_coeffs :: Exp -> Int -> Proof 
lemma_coeffs Var x          =   () 
lemma_coeffs (Con i) _      =   () 
lemma_coeffs (Add e1 e2) x  =   lemma_coeffs e1 x 
                            &&& lemma_coeffs e2 x 
                            &&& lemma_add_poly (coeffs e1) (coeffs e2) x 
lemma_coeffs (Mul e1 e2) x  =   lemma_coeffs e1 x 
                            &&& lemma_coeffs e2 x 
                            &&& lemma_mul_poly (coeffs e1) (coeffs e2) x 
