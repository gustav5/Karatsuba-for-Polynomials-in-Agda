import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _<?_; _⊓_)
open import Data.Nat.DivMod
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer.Base 
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
take _ [] = []
take zero _ = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {A : Set} → ℕ → List A → List A
drop (suc n) (x ∷ xs) = drop n xs
drop zero xs = xs
drop _ [] = []
  
replicate : ∀ {A : Set} → ℕ → A → List A
replicate zero _ = []
replicate (suc n) x = x ∷ replicate n x


shift_right : ℕ → List ℤ → List ℤ
shift_right n xs = (replicate n +0) ++ xs

addPoly : List ℤ → List ℤ → List ℤ
addPoly [] [] = []
addPoly xs [] = xs
addPoly [] ys = ys
addPoly (x ∷ xs) (y ∷ ys) = x + y ∷ addPoly xs ys 


record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

{-# COMPILE GHC Pair = data (,) ((,)) #-}


splitAt : ∀ {A : Set} → ℕ → List A →  Pair (List A) (List A) 
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

--------------------------
--------------------------
-- Karatsuba


karatsuba' : ℕ → List ℤ → List ℤ → List ℤ
karatsuba' n [] ys = []
karatsuba' n xs [] = []
karatsuba' n [ x ] [ y ] = mulPoly [ x ] [ y ]
karatsuba' zero xs ys = mulPoly xs ys
karatsuba' n [ x ] ys = map (x *_) ys
karatsuba' n xs [ y ] = map (y *_) xs
karatsuba' _ (x1 ∷ x2 ∷ []) ys = mulPoly (x1 ∷ x2 ∷ []) ys
karatsuba' _ xs (y1 ∷ y2 ∷ []) = mulPoly xs (y1 ∷ y2 ∷ [])
karatsuba' (suc n) xs ys = let m = ((length xs / 2) Data.Nat.⊓ (length ys / 2)) in
                  let ba = splitAt m xs in
                  let dc = splitAt m ys in
                  let ac = karatsuba' n (Pair.snd ba) (Pair.snd dc) in 
                  let bd = karatsuba' n (Pair.fst ba) (Pair.fst dc) in
                  let a_plus_b = addPoly (Pair.snd ba) (Pair.fst ba) in
                  let c_plus_d = addPoly (Pair.snd dc) (Pair.fst dc) in
                  let ad_plus_bc = (subPoly (subPoly (karatsuba' n a_plus_b c_plus_d) ac) bd) in
                  addPoly (addPoly (shift_right (2 Data.Nat.* m) ac) (shift_right m ad_plus_bc)) bd


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

kara_right_empty : ∀ (n : ℕ) (xs : List ℤ)
  → karatsuba' n xs [] ≡ []
kara_right_empty n []  = refl
kara_right_empty n (x ∷ xs) = refl


mulPoly_right_empty : ∀ (xs : List ℤ)
  → mulPoly xs [] ≡ []
mulPoly_right_empty [] = refl
mulPoly_right_empty (x ∷ xs) = refl


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
   



--------------------------
---------------   in progress

kara_zero : ∀ (xs ys : List ℤ)
  → karatsuba' zero xs ys ≡ mulPoly xs ys
kara_zero [] ys = refl
    

kara_zero (x ∷ xs) ys =
  begin
    karatsuba' zero (x ∷ xs) ys
  ≡⟨⟩
    {!!}

map_kara_right : ∀ (n : ℕ) (x : ℤ) (ys : List ℤ)
  → map (x *_) ys ≡ karatsuba' n [ x ] ys 
map_kara_right n x [] = refl
map_kara_right n x (y ∷ ys) =
  begin
    map (x *_) (y ∷ ys)
  ≡⟨⟩   
    x * y ∷ map (x *_) ys
  ≡⟨ cong ((x * y) ∷_) (map_kara_right n x ys) ⟩
    x * y ∷ karatsuba' n [ x ] ys
  ≡⟨⟩
    {!!}



kara_head : ∀ (n : ℕ) (x y : ℤ) (xs ys : List ℤ)
  → x * y ∷ (karatsuba' n xs ys) ≡ karatsuba' n (x ∷ xs) (y ∷ ys) 
kara_head n x y [] ys =
  begin
   x * y ∷ karatsuba' n [] ys
  ≡⟨⟩
    [ x * y ]
  ≡⟨ mul-mulPoly x y ⟩
    mulPoly [ x ] [ y ]
  ≡⟨⟩
    {!!}



test1 : ∀ (n : ℕ) (x y : ℤ) (ys : List ℤ)
  → karatsuba' n [ x ] (y ∷ ys) ≡ x * y ∷ karatsuba' n [ x ] ys 
test1 n x y [] =
  begin
    karatsuba' n [ x ] (y ∷ [])
  ≡⟨⟩
    mulPoly [ x ] [ y ]
  ≡⟨⟩
    addPoly (map (x *_) [ y ]) ( +0 ∷  mulPoly [] [ y ])
  ≡⟨⟩
    addPoly ((x * y) ∷ []) (+0 ∷ [])
  ≡⟨⟩
    ((x * y) + +0) ∷ addPoly [] []
  ≡⟨ cong ( _∷ addPoly [] []) (+-identityʳ (x * y)) ⟩
    x * y ∷ addPoly [] []
  ≡⟨⟩
    [ x * y ]
  ∎
  
test1 n x y (z ∷ zs) =
  begin
    karatsuba' n [ x ] (y ∷ z ∷ zs)
  ≡⟨⟩
    {!!}


kara_map_r : ∀ (n : ℕ) (y : ℤ) (xs : List ℤ)
  → karatsuba' n xs [ y ] ≡ map (y *_) xs
kara_map_r n xs y = {!!}




---------------------------------
-------------------  proof in progress


ismul' : ∀ (n : ℕ) (xs ys : List ℤ)
  → karatsuba' n xs ys ≡ mulPoly xs ys
ismul' n [] ys =
  begin
    karatsuba' n [] ys
  ≡⟨⟩
    []
  ≡⟨⟩
     mulPoly [] ys
  ∎
ismul' n xs [] =
  begin
    karatsuba' n xs []
  ≡⟨ kara_right_empty n xs ⟩
    []
  ≡⟨ sym (mulPoly_right_empty xs) ⟩
    mulPoly xs []
  ∎
ismul' n [ x ] [ y ] = --- added this, helped me a little bit in kara_head, but not sure if
  begin                --- this is smart
    karatsuba' n [ x ] [ y ]
   ≡⟨⟩
     mulPoly [ x ] [ y ]
   ∎
ismul' zero xs ys =
  begin
    karatsuba' zero xs ys
  ≡⟨⟩
    {!!}
ismul' n [ x ] ys =
  begin
    karatsuba' n [ x ] ys
  ≡⟨⟩
   {!!}





