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




record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

{-# COMPILE GHC Pair = data (,) ((,)) #-}


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
karatsuba' (suc n) xs ys with (((length xs / 2) Data.Nat.⊓ (length ys / 2)) ≤ᵇ 2)
...               | true = mulPoly xs ys
...               | false = let m = ((length xs / 2) Data.Nat.⊓ (length ys / 2)) in
                  let ba = splitAt m xs in
                  let dc = splitAt m ys in
                  let ac = karatsuba' n (Pair.snd ba) (Pair.snd dc) in 
                  let bd = karatsuba' n (Pair.fst ba) (Pair.fst dc) in
                  let a_plus_b = addPoly (Pair.snd ba) (Pair.fst ba) in
                  let c_plus_d = addPoly (Pair.snd dc) (Pair.fst dc) in
                  let ad_plus_bc = (subPoly (subPoly (karatsuba' n a_plus_b c_plus_d) ac) bd) in
                  addPoly (addPoly (shiftRight (2 Data.Nat.* m) ac) (shiftRight m ad_plus_bc)) bd


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
  →  (Pair.fst (splitAt m xs)) +p (shiftRight m (Pair.snd (splitAt m xs))) ≡ xs
split_p  zero xs =
  begin
    (Pair.fst (splitAt zero xs)) +p (shiftRight zero (Pair.snd (splitAt zero xs)))
  ≡⟨ cong ( _+p (shiftRight zero (Pair.snd (splitAt zero xs)))) (cong Pair.fst (splitAtZero xs)) ⟩
    [] +p (shiftRight zero (Pair.snd (splitAt zero xs)))
  ≡⟨ cong ([] +p_ ) (shiftRightZero (Pair.snd (splitAt zero xs))) ⟩
    [] +p xs
  ≡⟨ +p_empty_l xs ⟩
    xs
  ∎
  
split_p (suc m) xs =
  begin
    (Pair.fst (splitAt (ℕ.suc m) xs)) +p (shiftRight (ℕ.suc m) (Pair.snd (splitAt (ℕ.suc m) xs)))
  ≡⟨⟩
 --   (Pair.fst ( take (ℕ.suc m) xs , drop (ℕ.suc m) xs ))  +p (shiftRight (ℕ.suc m) (Pair.snd (splitAt (ℕ.suc m) xs)))
--  ≡⟨⟩
    {!!}
--    (Pair.fst (splitAt (ℕ.suc m) xs)) +p ((replicate (ℕ.suc m)) ++ (Pair.snd (splitAt (ℕ.suc m) xs)))
--  ≡⟨⟩
--    {!!}


shiftRightLemma :  ∀ (m : ℕ)
  → shiftRight m (Pair.snd ( splitAt m [])) ≡ (Pair.snd ( splitAt m []))
shiftRightLemma m =
  begin
    shiftRight m (Pair.snd ( splitAt m []))
  ≡⟨⟩
   -- (replicate m) ++ (Pair.snd ( splitAt m []))
 -- ≡⟨⟩
    {!!}


split_p_two : ∀ (m : ℕ) (xs : List ℤ)
  →   xs ≡ (Pair.fst (splitAt m xs)) +p (shiftRight m (Pair.snd (splitAt m xs)))
split_p_two  m [] =
  begin
    []
  ≡⟨⟩
    [] +p []
  ≡⟨⟩
    (Pair.fst (take m [] , drop m [])) +p []
  ≡⟨ cong (_+p []) (cong Pair.fst (sym (splitAt_empty m))) ⟩
    (Pair.fst ( splitAt m [])) +p []
  ≡⟨⟩
    (Pair.fst ( splitAt m [])) +p (Pair.snd (take m [] , drop m []))
  ≡⟨ cong ((Pair.fst ( splitAt m [])) +p_ ) (cong  Pair.snd (sym (splitAt_empty m))) ⟩ 
    (Pair.fst ( splitAt m [])) +p (Pair.snd ( splitAt m []))
  ≡⟨⟩
    {!!}
    
split_p_two m (x ∷ xs) = {!!}


--replicate : ∀ {A : Set} → ℕ → A → List A
--replicate zero _ = []
--replicate (suc n) x = x ∷ replicate n x
---------------------------------
-------------------  proof in progress




ismul' : ∀ (n : ℕ) (xs ys : List ℤ)
  → karatsuba' n xs ys ≡ mulPoly xs ys  
ismul' zero xs ys = refl
ismul' (suc n) xs ys with (((length xs / 2) Data.Nat.⊓ (length ys / 2)) ≤ᵇ 2)
...                   | true = refl
...                   | false =
                         begin
                           let m = ((length xs / 2) Data.Nat.⊓ (length ys / 2)) in
                           let ba = splitAt m xs in
                           let dc = splitAt m ys in
                           let ac = karatsuba' n (Pair.snd ba) (Pair.snd dc) in 
                           let bd = karatsuba' n (Pair.fst ba) (Pair.fst dc) in
                           let a_plus_b = addPoly (Pair.snd ba) (Pair.fst ba) in
                           let c_plus_d = addPoly (Pair.snd dc) (Pair.fst dc) in
                           let ad_plus_bc = (subPoly (subPoly (karatsuba' n a_plus_b c_plus_d) ac) bd) in
                           addPoly (addPoly (shiftRight (2 Data.Nat.* m) ac) (shiftRight m ad_plus_bc)) bd
                         ≡⟨⟩
                           addPoly (addPoly (shiftRight (2 Data.Nat.* m) ac) (shiftRight m ad_plus_bc)) bd
                         ≡⟨⟩
                           {!!}

