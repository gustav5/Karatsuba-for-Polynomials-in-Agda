import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _<?_; _⊓_) renaming(_*_ to _*ℕ_)
open import Data.Nat.DivMod
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer.Base hiding (_⊓_) 
open import Data.Integer.Properties
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
 




-------------------------------
-- Lists
-------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_



pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  ℕ.suc (length xs)

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)


reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym ( ++-identityʳ (reverse ys) ) ⟩
    reverse ys ++ []
  ≡⟨⟩
   reverse ys ++ reverse []
  ∎
  
reverse-++-distrib (x ∷ xs) ys = 
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong ( _++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) ([ x ]) ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀ {A : Set } (xs : List A) 
  → reverse (reverse xs) ≡ xs 
reverse-involutive [] =
  begin
    reverse (reverse [])  
  ≡⟨⟩
    reverse ([])
    ≡⟨⟩
    []
  ∎
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse ( reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    reverse (x ∷ []) ++ reverse (reverse xs)
  ≡⟨⟩
    reverse [] ++ [ x ] ++ reverse (reverse xs)
  ≡⟨⟩  
    [ x ] ++ reverse (reverse xs)
  ≡⟨ cong ( [ x ] ++_ ) (reverse-involutive xs)⟩
    [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎


----------------------------------
----------------------------------
-- functions

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

zipWith : ∀ {A B C : Set} → (A → B → C) → List A → List B → List C
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

take : ∀ {A : Set} → ℕ → List A → List A
take n [] = []
take zero n = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {A : Set} → ℕ → List A → List A
drop _ [] = []
drop zero xs = xs
drop (suc n) (x ∷ xs) = drop n xs


  
replicate : ℕ → List ℤ
replicate zero = []
replicate (suc n) = +0 ∷ replicate n 




shiftRight : ℕ → List ℤ → List ℤ
shiftRight n [] = []
shiftRight n xs = (replicate n) ++ xs

addPoly : List ℤ → List ℤ → List ℤ
addPoly [] [] = []
addPoly xs [] = xs
addPoly [] ys = ys
addPoly (x ∷ xs) (y ∷ ys) = x + y ∷ addPoly xs ys 

_+p_ : List ℤ → List ℤ → List ℤ
[] +p [] = []
xs +p [] = xs
[] +p ys = ys
(x ∷ xs) +p (y ∷ ys) = x + y ∷ (xs +p ys) 

_*p_ : List ℤ → List ℤ → List ℤ
_*p_ [] ys = []
_*p_ xs [] = []
_*p_ (x ∷ []) ys = (map (x *_) ys) 
_*p_ (x ∷ xs) ys = (map (x *_) ys) +p ( +0 ∷  xs *p ys)




record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

{-# COMPILE GHC Pair = data (,) ((,)) #-}
open Pair

splitAt : ℕ → List ℤ →  Pair (List ℤ) (List ℤ)
splitAt zero xs = ( [] , xs )
splitAt _ [] = ( [] , [] )
splitAt n xs = ( take n xs , drop n xs ) 

mulPoly : List ℤ → List ℤ → List ℤ
mulPoly [] ys = []
mulPoly xs [] = []
mulPoly (x ∷ xs) ys = addPoly (map (x *_) ys) ( +0 ∷  mulPoly xs ys)




negPoly : List ℤ → List ℤ
negPoly [] = []
negPoly (x ∷ xs) = (- x) ∷ negPoly xs

subPoly : List ℤ → List ℤ → List ℤ
subPoly xs ys = addPoly xs (negPoly ys)



a : List ℤ
a = [ + 1 , + 2 ]

b : List ℤ
b = [ + 3 , + 4 , + 5  ]



if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y


infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n

--------------------------
--------------------------
-- Karatsuba


karatsuba' : ℕ → List ℤ → List ℤ → List ℤ
karatsuba' zero xs ys = mulPoly xs ys
karatsuba' (suc n) xs ys = if (((length xs / 2) ⊓ (length ys / 2)) ≤ᵇ 2)
                           then (mulPoly xs ys)
                           else
                           let m = ((length xs / 2) ⊓ (length ys / 2)) in
                           let (b , a) = splitAt m xs in
                           let (d , c) = splitAt m ys in
                           let ac = karatsuba' n a c in 
                           let bd = karatsuba' n b d in
                           let a_plus_b = addPoly a b in
                           let c_plus_d = addPoly c d in
                           let ad_plus_bc = (subPoly (subPoly (karatsuba' n a_plus_b c_plus_d) ac) bd) in
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd


karatsuba : List ℤ → List ℤ → List ℤ
karatsuba [] ys = []
karatsuba xs [] = []
karatsuba xs ys = karatsuba' ((length xs) Data.Nat.⊔ (length ys)) xs ys




mulPoly' : ℕ → List ℤ → List ℤ → List ℤ
mulPoly' n [] ys = []
mulPoly' n xs [] = []
mulPoly' n (x ∷ xs) ys = addPoly (map (x *_) ys) ( +0 ∷  mulPoly' n xs ys)



----------------------------------
-------------- working help functions



mulPoly_right_empty : ∀ (xs : List ℤ)
  → mulPoly xs [] ≡ []
mulPoly_right_empty [] = refl
mulPoly_right_empty (x ∷ xs) = refl


*pRightEmpty : ∀ (xs : List ℤ)
  → xs *p [] ≡ []
*pRightEmpty []  = refl
*pRightEmpty (x ∷ xs) = refl

*pLeftEmpty : ∀ (xs : List ℤ)
  → [] *p xs ≡ []
*pLeftEmpty []  = refl
*pLeftEmpty (x ∷ xs) = refl
 

mul-mulPoly : ∀ (x y : ℤ)
  → [ x * y ] ≡ mulPoly [ x ] [ y ]
mul-mulPoly x y =
  begin
     x * y ∷ []
  ≡⟨ cong ( _∷ []) ( sym (+-identityʳ (x * y))) ⟩
    ( x * y + +0) ∷ []
  ≡⟨⟩
    [ x * y + +0 ]
  ∎

addPoly_empty_r : ∀ (xs : List ℤ)
  → addPoly xs [] ≡ xs
addPoly_empty_r []  = refl
addPoly_empty_r (x ∷ xs) = refl


mulPoly-map : ∀ (x : ℤ) (ys : List ℤ)
  → mulPoly [ x ] ys ≡ map (x *_) ys
mulPoly-map x [] = refl
mulPoly-map x (y ∷ ys) =
  begin
    mulPoly [ x ] (y ∷ ys)
  ≡⟨⟩
    mulPoly (x ∷ []) (y ∷ ys)
  ≡⟨⟩
    addPoly (map (x *_) (y ∷ ys)) ( +0 ∷ mulPoly [] (y ∷ ys))
  ≡⟨⟩
    addPoly (x * y ∷ map (x *_) ys) [ +0 ] 
  ≡⟨⟩
    x * y + +0 ∷ addPoly (map (x *_) ys) []
  ≡⟨ cong ((x * y + +0) ∷_) (addPoly_empty_r (map (x *_) ys)) ⟩
    x * y + +0 ∷ map (x *_) ys
  ≡⟨ cong ( _∷ map (x *_) ys) (+-identityʳ (x * y)) ⟩
   x * y ∷ map (x *_) ys
  ∎
   

+p_empty_r : ∀ (xs : List ℤ)
  → xs +p [] ≡ xs
+p_empty_r []  = refl
+p_empty_r (x ∷ xs) = refl

+p_empty_l : ∀ (xs : List ℤ)
  → [] +p xs ≡ xs
+p_empty_l []  = refl
+p_empty_l (x ∷ xs) = refl

--repli_rec : ∀ (n : ℕ) (x : ℤ)
--  → replicate (ℕ.suc n) ≡ x ∷ replicate n 
--repli_rec zero = refl
--repli_rec (ℕ.suc n) = refl

--shiftRight : ℕ → List ℤ → List ℤ
--shiftRight n xs = (replicate n) ++ xs

--replicate : ℕ → List ℤ
--replicate zero = []
--replicate (suc n) = +0 ∷ replicate n

--repli_rec : ∀ (n : ℕ) (xs : List ℤ)
--  → replicate (ℕ.suc n) xs ≡ +0 ∷ replicate n xs 
--repli_rec ℕ.zero xs = refl
--repli_rec (ℕ.suc n) xs = refl

--shiftRreplicateZero ∀ (xs : List ℤ)
--  shiftRight zero xs ≡ r

shiftRightZero : ∀ (xs : List ℤ)
  → shiftRight zero xs ≡ xs
shiftRightZero [] = refl
shiftRightZero (x ∷ xs) = refl

shiftRightEmpty : ∀ (n : ℕ)
  → shiftRight n [] ≡ []
shiftRightEmpty n = refl


shiftRightReplicateZero : ∀ (xs : List ℤ)
  → shiftRight zero xs ≡ replicate zero ++ xs
shiftRightReplicateZero [] = refl
shiftRightReplicateZero (x ∷ xs) = refl


shiftRightOne : ∀ (xs : List ℤ)
  → shiftRight (ℕ.suc zero) xs ≡ +0 ∷ xs
shiftRightOne xs =
  begin
    shiftRight (ℕ.suc zero) xs
  ≡⟨⟩
 --   replicate (ℕ.suc zero) ++ xs 
 -- ≡⟨⟩
    {!!}

replShiftOne : ∀ (xs : List ℤ)
  → replicate (ℕ.suc zero) ++ xs ≡ shiftRight (ℕ.suc zero) xs
replShiftOne xs =
  begin
    +0 ∷ xs
  ≡⟨ cong (+0 ∷_) (sym (shiftRightReplicateZero xs)) ⟩
    +0 ∷ shiftRight zero xs
  ≡⟨⟩
   {!!} -- shiftRight 1 xs
  
    

shiftRight++ : ∀ (n : ℕ) (xs : List ℤ)
  → +0 ∷ shiftRight n xs ≡ shiftRight (ℕ.suc n) xs
shiftRight++ zero xs =
  begin
    +0 ∷ shiftRight zero xs
  ≡⟨ cong (+0 ∷_) (shiftRightReplicateZero xs) ⟩
    +0 ∷ replicate zero ++ xs
  ≡⟨⟩
    replicate (ℕ.suc zero) ++ xs
  ≡⟨⟩
   -- shiftRight (ℕ.suc zero) xs
  -- ≡⟨⟩
    {!!}



shiftRightReplicate : ∀ (n : ℕ) (xs : List ℤ)
  → (replicate n ) ++ xs ≡ shiftRight n xs 
shiftRightReplicate zero xs =
  begin
    replicate zero ++ xs
  ≡⟨⟩
    xs
  ≡⟨ sym (shiftRightZero xs) ⟩
    shiftRight zero xs
  ∎
shiftRightReplicate (suc n) xs =
  begin
    replicate (ℕ.suc n) ++ xs
  ≡⟨⟩
    +0 ∷ replicate n  ++ xs
  ≡⟨ cong (+0 ∷_) (shiftRightReplicate n xs)⟩
    +0 ∷ shiftRight n xs
  ≡⟨⟩
    {!!}
    
    
    
--shiftR_repli : ∀ (n : ℕ) 
--  → shiftRight n [] ≡ (replicate n) ++ []
--shiftR_repli zero  = refl
--shiftR_repli (ℕ.suc n) = refl

splitAt_empty : ∀ (n : ℕ) 
  → splitAt n [] ≡ ( take n [] , drop n [] )
splitAt_empty zero  = refl
splitAt_empty (ℕ.suc n) = refl

splitAtZero : ∀ (xs : List ℤ)
  → splitAt zero xs ≡ ( [] , xs ) 
splitAtZero [] = refl
splitAtZero xs = refl

takeZero : ∀ (xs : List ℤ)
  → take zero xs ≡ []
takeZero [] = refl
takeZero (x ∷ xs) = refl

dropZero : ∀ (xs : List ℤ)
  → drop zero xs ≡ xs
dropZero [] = refl
dropZero (x ∷ xs) = refl

splitAt_n : ∀ (n : ℕ) (x : ℤ) (xs : List ℤ)
  → splitAt (ℕ.suc n) (x ∷ xs) ≡ ( (x ∷ (take n xs)) , drop n xs ) 
splitAt_n n x xs = refl 



--------------------------
---------------   in progress

splitAtRec : ∀ (n : ℕ) (xs : List ℤ)
  → splitAt n xs ≡ ( take n xs , drop n xs )
splitAtRec zero (x ∷ xs) =
  begin
    splitAt zero (x ∷ xs)
  ≡⟨ splitAtZero (x ∷ xs) ⟩
    ( [] , (x ∷ xs) ) 
  ≡⟨⟩
    ( take zero (x ∷ xs) ,  drop zero (x ∷ xs) ) 
  ∎
splitAtRec (ℕ.suc zero) (x ∷ xs) = {!!}
splitAtRec (ℕ.suc n) (x ∷ xs) =
  begin
    splitAt (ℕ.suc n) (x ∷ xs)
  ≡⟨⟩
   {!!}




splitAtTwo : ∀ (n : ℕ) (xs : List ℤ)
  → splitAt n xs ≡ ( take n xs , drop n xs )

splitAtTwo n [] =
  begin
    splitAt n []
  ≡⟨ splitAt_empty n ⟩
   ( take n [] , drop n [] )
  ∎
splitAtTwo n (x ∷ xs) =
  begin
    splitAt n (x ∷ xs)
  ≡⟨⟩
    {!!}



--splitAt : ℕ → List ℤ →  Pair (List ℤ) (List ℤ)
--splitAt zero xs = ( [] , xs )
--splitAt _ [] = ( [] , [] )
--splitAt n xs = ( take n xs , drop n xs ) 

-- shiftRight : ℕ → List ℤ → List ℤ
-- shiftRight n xs = (replicate n +0) ++ xs

--take : ∀ {A : Set} → ℕ → List A → List A
--take _ [] = []
--take zero _ = []
--take (suc n) (x ∷ xs) = x ∷ take n xs

--drop : ∀ {A : Set} → ℕ → List A → List A
--drop (suc n) (x ∷ xs) = drop n xs
--drop zero xs = xs
--drop _ [] = []

splitTakeDrop : ∀ (n : ℕ) (xs : List ℤ)
  → splitAt (ℕ.suc n) xs ≡ ( take n xs , drop n xs ) 
splitTakeDrop zero xs =
  begin
    {!!}
--    splitAt zero xs
--  ≡⟨ splitAtZero xs ⟩
--    ( [] , xs )
--  ≡⟨ cong ( _, xs ) (sym (takeZero xs))  ⟩
--    ( take zero xs , xs )
--  ≡⟨ cong ( take zero xs ,_ ) (sym (dropZero xs))⟩
 --   ( take zero xs , drop zero xs )
 -- ∎
--splitTakeDrop (ℕ.suc n) [ x ] = {!!}
--splitTakeDrop (ℕ.suc n) (x ∷ xs) =
--  begin
--    splitAt (ℕ.suc n) (x ∷ xs)
--  ≡⟨⟩
--    {!!}
    


split_p : ∀ (m : ℕ) (xs : List ℤ)
  →  (fst (splitAt m xs)) +p (shiftRight m (snd (splitAt m xs))) ≡ xs
split_p  zero xs =
  begin
    (fst (splitAt zero xs)) +p (shiftRight zero (snd (splitAt zero xs)))
  ≡⟨ cong ( _+p (shiftRight zero (snd (splitAt zero xs)))) (cong fst (splitAtZero xs)) ⟩
    [] +p (shiftRight zero (snd (splitAt zero xs)))
  ≡⟨ cong ([] +p_ ) (shiftRightZero (snd (splitAt zero xs))) ⟩
    [] +p xs
  ≡⟨ +p_empty_l xs ⟩
    xs
  ∎
  
split_p (suc m) xs =
  begin
    (fst (splitAt (ℕ.suc m) xs)) +p (shiftRight (ℕ.suc m) (snd (splitAt (ℕ.suc m) xs)))
  ≡⟨⟩
 --   (fst ( take (ℕ.suc m) xs , drop (ℕ.suc m) xs ))  +p (shiftRight (ℕ.suc m) (snd (splitAt (ℕ.suc m) xs)))
--  ≡⟨⟩
    {!!}
--    (fst (splitAt (ℕ.suc m) xs)) +p ((replicate (ℕ.suc m)) ++ (snd (splitAt (ℕ.suc m) xs)))
--  ≡⟨⟩
--    {!!}


shiftRightLemma :  ∀ (m : ℕ)
  → shiftRight m (snd ( splitAt m [])) ≡ (snd ( splitAt m []))
shiftRightLemma m =
  begin
    shiftRight m (snd ( splitAt m []))
  ≡⟨⟩
   -- (replicate m) ++ (snd ( splitAt m []))
 -- ≡⟨⟩
    {!!}


split-p-two : ∀ (m : ℕ) (xs : List ℤ)
  →   xs ≡ (fst (splitAt m xs)) +p (shiftRight m (snd (splitAt m xs)))
split-p-two  m [] =
  begin
    []
  ≡⟨⟩
    [] +p [] 
  ≡⟨⟩
    (fst (take m [] , drop m [])) +p []
  ≡⟨ cong (_+p []) (cong fst (sym (splitAt_empty m))) ⟩
    (fst ( splitAt m [])) +p []
  ≡⟨⟩
    (fst ( splitAt m [])) +p (snd (take m [] , drop m []))
  ≡⟨ cong ((fst ( splitAt m [])) +p_ ) (cong  snd (sym (splitAt_empty m))) ⟩ 
    (fst ( splitAt m [])) +p (snd ( splitAt m []))
  ≡⟨⟩
    {!!}
    
split-p-two m (x ∷ xs) = {!!}


--replicate : ∀ {A : Set} → ℕ → A → List A
--replicate zero _ = []
--replicate (suc n) x = x ∷ replicate n x
---------------------------------
-------------------  proof in progress
-- +p_empty_l
-- *pLeftEmpty

--+p_empty_r : ∀ (xs : List ℤ)
--  → xs +p [] ≡ xs
--+p_empty_r []  = refl
--+p_empty_r (x ∷ xs) = refl

--+p_empty_l : ∀ (xs : List ℤ)
--  → [] +p xs ≡ xs
--+p_empty_l []  = refl
--+p_empty_l (x ∷ xs) = refl

--_+p_ : List ℤ → List ℤ → List ℤ
--[] +p [] = []
--xs +p [] = xs
--[] +p ys = ys
--(x ∷ xs) +p (y ∷ ys) = x + y ∷ (xs +p ys) 
--
--_*p_ : List ℤ → List ℤ → List ℤ
--_*p_ [] ys = []
--_*p_ xs [] = []
--_*p_ (x ∷ xs) ys = addPoly (map (x *_) ys) ( +0 ∷  xs *p ys)


--_++_ : ∀ {A : Set} → List A → List A → List A
--[]       ++ ys  =  ys
-- (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)


--*pLeftEmpty : ∀ (xs : List ℤ)
--  → [] *p xs ≡ []
--*pLeftEmpty []  = refl
--*pLeftEmpty (x ∷ xs) = refl


--+p-comm ∀ 

*p-map : ∀ (x y : ℤ) (xs ys : List ℤ)
  → (x ∷ xs) *p (y ∷ ys) ≡ (map (x *_) ys) +p (+0 ∷ (xs *p ys))
*p-map x y [] ys =
  begin
    x * y ∷ map (x *_) ys
  ≡⟨⟩
   map (x *_) (y ∷ ys)
  ≡⟨ {!!} ⟩ -- plus 0
   map (x *_) ys +p [ +0 ]
  ∎


*p-map x y (z ∷ zs) ys =
  begin
    x * y + +0 ∷ (map (_*_ x) ys +p ((z ∷ zs) *p (y ∷ ys)))
  ≡⟨ {!!} ⟩ --get rid of +0
     x * y ∷ ((map (x *_) ys) +p ((z ∷ zs) *p (y ∷ ys)))
  ≡⟨ {!!} ⟩ --cong (x * y ∷_) (cong ((map (x *_) ys) +p_) (*p-map z y zs ys))
    (map (x *_) (y ∷ ys) +p (map (z *_) ys +p (+0 ∷ (zs *p ys))))
  ≡⟨ {!!} ⟩
    (map (x *_) (y ∷ ys) +p (((z ∷ []) *p ys) +p (+0 ∷ (zs *p ys))))
  ≡⟨ {!!} ⟩
   
   (map (x *_) ys +p (+0 ∷ ((z ∷ zs) *p ys)))
  ∎
*p-comm : ∀ (xs ys : List ℤ) 
  → xs *p ys ≡  ys *p xs
*p-comm (x ∷ xs) [] = refl
*p-comm [] ys =
  begin
    [] *p ys
  ≡⟨ *pLeftEmpty ys ⟩
    []
  ≡⟨ sym (*pRightEmpty ys) ⟩
    ys *p []
  ∎
*p-comm (x ∷ xs) (y ∷ ys) =
  begin
    ((x ∷ xs) *p (y ∷ ys))
  ≡⟨ {!!} ⟩ -- *p-map
    (map (x *_) (y ∷ ys)) +p ( +0 ∷  xs *p (y ∷ ys))
  ≡⟨ cong ((map (x *_) (y ∷ ys)) +p_) (cong (+0 ∷_) (*p-comm xs (y ∷ ys))) ⟩
    (map (x *_) (y ∷ ys)) +p ( +0 ∷  (y ∷ ys) *p xs)
  ≡⟨ {!!} ⟩
     x * y + +0 ∷ (map (x *_) ys +p ((y ∷ ys) *p xs))
  ≡⟨ {!!} ⟩ --bort med +
    x * y  ∷ ((map (x *_) ys +p ((y ∷ ys) *p xs)))
  ≡⟨ {!!} ⟩
    ( +0 ∷  ys *p xs) +p (map (y *_) xs)
  ≡⟨ {!!} ⟩
    (map (y *_) xs) +p ( +0 ∷  ys *p xs)
  ≡⟨ {!!} ⟩
    ((y ∷ ys) *p (x ∷ xs))
  ∎
  --   +0 ∷ (map (y *_) xs) +p ( +0 ∷  ys *p xs) +p (map (x *_) (y ∷ ys))
 -- ≡⟨⟩
 --    +0 ∷ (map (y *_) xs) +p ( +0 ∷  ys *p xs) +p (x + y) ∷ (map (x *_) (ys))
 -- ≡⟨⟩
 --   (map (y *_) xs

 --   (x * y) +0 ∷ (map (x *_) ys) +p ( +0 ∷  (y ∷ ys) *p xs )
 -- ≡⟨⟩
 --   (y * x) ∷ (map (x *_) ys) +p ( +0 ∷  (y ∷ ys) *p xs )
 -- ≡⟨⟩
  --  (x * ys) ∷ (map (x *_) ys  +p ( +0 ∷  (map (y *_) xs) +p ( +0 ∷  ys *p xs))
    
distrib : ∀ (xs ys zs : List ℤ)
  → xs *p (ys +p zs) ≡ (xs *p ys) +p (xs *p zs)
distrib xs [] zs =
  begin
    (xs *p ([] +p zs))
  ≡⟨ cong (xs *p_) ( +p_empty_l zs) ⟩
    (xs *p zs)
  ≡⟨ sym (+p_empty_l (xs *p zs)) ⟩
    [] +p (xs *p zs)   
  ≡⟨ cong (_+p (xs *p zs)) (sym (*pRightEmpty xs)) ⟩
    ((xs *p []) +p (xs *p zs))
  ∎



distrib xs (y ∷ ys) zs =
  begin
    (xs *p ((y ∷ ys) +p zs))
  ≡⟨ {!!} ⟩
    ((xs *p (y ∷ ys)) +p (xs *p zs))
  ∎



distribBig : ∀ (xs ys zs rs : List ℤ)
  → (xs +p ys) *p (zs +p rs) ≡ (xs *p zs) +p ((xs *p rs) +p ((ys *p zs) +p (ys *p rs)))
distribBig [] ys zs rs =
  begin
    ([] +p ys) *p (zs +p rs)
  ≡⟨ cong (_*p (zs +p rs)) (+p_empty_l ys) ⟩
    ys *p (zs +p rs)
  ≡⟨ distrib ys zs rs ⟩
   ((ys *p zs) +p (ys *p rs))
  ≡⟨⟩
    {!!}

distribBig (x ∷ xs) ys zs rs = {!!}

ismul' : ∀ (n : ℕ) (xs ys : List ℤ)
  → mulPoly xs ys ≡ karatsuba' n xs ys  
ismul' zero xs ys = refl
ismul' (suc n) xs ys with (((length xs / 2) ⊓ (length ys / 2)) ≤ᵇ 2)
...                   | true = refl
...                   | false =
                         begin
                           let m = ((length xs / 2) ⊓ (length ys / 2)) in
                           let (b , a) = splitAt m xs in
                           let (d , c) = splitAt m ys in
                           let ac = karatsuba' n a c in 
                           let bd = karatsuba' n b d in
                           let a_plus_b = addPoly a b in
                           let c_plus_d = addPoly c d in
                           let ad_plus_bc = (subPoly (subPoly (karatsuba' n a_plus_b c_plus_d) ac) bd) in
                           mulPoly xs ys
                         ≡⟨ cong₂ mulPoly (split-p-two m xs) (split-p-two m ys) ⟩
                           mulPoly (b +p shiftRight m a) (d +p shiftRight m c)
                         ≡⟨ {!!} ⟩
                           (((mulPoly (shiftRight m a) (shiftRight m c)) +p (mulPoly (shiftRight m c) d)) +p  (mulPoly b (shiftRight m c))) +p (mulPoly b d)
                         ≡⟨ {!!} ⟩
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd ∎
                           

