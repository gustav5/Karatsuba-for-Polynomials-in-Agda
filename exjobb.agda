import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _<?_; _⊓_;_≤_;z≤n; s≤s) renaming(_*_ to _*ℕ_ )
open import Data.Nat.DivMod
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer.Base hiding (_⊓_) 
open import Data.Integer.Properties
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
 

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

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)


----------------------------------
----------------------------------
-- functions
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  ℕ.suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

zipWith : ∀ {A B C : Set} → (A → B → C) → List A → List B → List C
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

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
shiftRight zero xs = xs
shiftRight (suc n) xs = +0 ∷ shiftRight n xs

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
_*p_ (x ∷ xs) ys = (map (x *_) ys) +p ( +0 ∷  xs *p ys)


negPoly : List ℤ → List ℤ
negPoly [] = []
negPoly (x ∷ xs) = (- x) ∷ negPoly xs

_-p_ : List ℤ → List ℤ → List ℤ
_-p_ xs ys = xs +p (negPoly ys)

subPoly : List ℤ → List ℤ → List ℤ
subPoly xs ys = addPoly xs (negPoly ys)

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



if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y


infix 4 _≤ᵇ'_

_≤ᵇ'_ : ℕ → ℕ → Bool
zero ≤ᵇ' n       =  true
suc m ≤ᵇ' zero   =  false
suc m ≤ᵇ' suc n  =  m ≤ᵇ' n

--------------------------
--------------------------
-- Karatsuba


karatsuba' : ℕ → List ℤ → List ℤ → List ℤ
karatsuba' zero xs ys = xs *p ys
karatsuba' (suc n) xs ys = if (((length xs / 2) ⊓ (length ys / 2)) ≤ᵇ' 2)
                           then (xs *p ys)
                           else
                           let m = ((length xs / 2) ⊓ (length ys / 2)) in
                           let (b , a) = splitAt m xs in
                           let (d , c) = splitAt m ys in
                           let ac = karatsuba' n a c in 
                           let bd = karatsuba' n b d in
                           let a_plus_b = addPoly a b in
                           let c_plus_d = addPoly c d in
                           let ad_plus_bc = ((karatsuba' n a_plus_b c_plus_d) -p ac) -p bd in
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd


karatsuba : List ℤ → List ℤ → List ℤ
karatsuba [] ys = []
karatsuba xs [] = []
karatsuba xs ys = karatsuba' ((length xs) Data.Nat.⊔ (length ys)) xs ys


----------------------------------
-------------- working help functions


*pRightEmpty : ∀ (xs : List ℤ)
  → xs *p [] ≡ []
*pRightEmpty []  = refl
*pRightEmpty (x ∷ xs) = refl

*pLeftEmpty : ∀ (xs : List ℤ)
  → [] *p xs ≡ []
*pLeftEmpty []  = refl
*pLeftEmpty (x ∷ xs) = refl

+pRightEmpty : ∀ (xs : List ℤ)
  → xs +p [] ≡ xs
+pRightEmpty [] = refl
+pRightEmpty (x ∷ xs) = refl

+pLeftEmpty : ∀ (xs : List ℤ)
  → [] +p xs ≡ xs
+pLeftEmpty []  = refl
+pLeftEmpty (x ∷ xs) = refl

+pOne : ∀ (x y : ℤ)
  → [ x ] +p [ y ] ≡ [ x + y ]
+pOne x y = refl

shiftRightZero : ∀ (xs : List ℤ)
  → shiftRight zero xs ≡ xs
shiftRightZero [] = refl
shiftRightZero (x ∷ xs) = refl
  
shiftRightReplicateZero : ∀ (xs : List ℤ)
  → shiftRight zero xs ≡ replicate zero ++ xs
shiftRightReplicateZero [] = refl
shiftRightReplicateZero (x ∷ xs) = refl

splitAtEmpty : ∀ (n : ℕ) 
  → splitAt n [] ≡ ( take n [] , drop n [] )
splitAtEmpty zero  = refl
splitAtEmpty (ℕ.suc n) = refl

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

splitAt-n : ∀ (n : ℕ) (x : ℤ) (xs : List ℤ)
  → splitAt (ℕ.suc n) (x ∷ xs) ≡ ( (x ∷ (take n xs)) , drop n xs ) 
splitAt-n n x xs = refl 


*p-map-left-single : ∀ (x : ℤ) (ys : List ℤ)
  → [ x ] *p ys ≡ map (x *_) ys
*p-map-left-single x [] = refl
*p-map-left-single x (y ∷ ys) =
  begin
    [ x ] *p (y ∷ ys)
  ≡⟨⟩
    (x ∷ []) *p (y ∷ ys)
  ≡⟨⟩
    (map (x *_) (y ∷ ys)) +p ( +0 ∷ mulPoly [] (y ∷ ys))
  ≡⟨⟩
    (x * y ∷ map (x *_) ys) +p [ +0 ] 
  ≡⟨⟩
    x * y + +0 ∷ (map (x *_) ys) +p []
  ≡⟨ cong ((x * y + +0) ∷_) (+pRightEmpty (map (x *_) ys)) ⟩
    x * y + +0 ∷ map (x *_) ys
  ≡⟨ cong ( _∷ map (x *_) ys) (+-identityʳ (x * y)) ⟩
   x * y ∷ map (x *_) ys
  ∎


addOne : ∀ (x : ℤ) (xs : List ℤ)
  →  x ∷ xs ≡ [ x ] +p (+0 ∷ xs) 
addOne x [] rewrite +-identityʳ x = refl
addOne x (y ∷ ys) rewrite +-identityʳ x = refl





--------------------------
---------------   in progress
   

negPoly-lemma : ∀ (xs : List ℤ)
  → xs +p (negPoly xs) ≡ shiftRight (length xs) []
negPoly-lemma [] = refl
negPoly-lemma (x ∷ xs) =
  begin
     x + - x ∷ (xs +p negPoly xs)
  ≡⟨ {!!} ⟩
    +0 ∷ (xs +p negPoly xs)
  ≡⟨ cong (+0 ∷_) (negPoly-lemma xs) ⟩
    +0 ∷ shiftRight (length xs) []
  ∎

xs-take-drop : ∀  (n : ℕ) (xs : List ℤ)
  → (take n xs) +p (shiftRight n (drop n xs)) ≡ xs
xs-take-drop zero xs rewrite takeZero xs | dropZero xs | +pLeftEmpty xs = refl
xs-take-drop (ℕ.suc n) (x ∷ xs) rewrite +-identityʳ x | xs-take-drop n xs = refl 
xs-take-drop n xs = {!!}


-------------------------------------------
---------------- properties

+p-assoc : ∀ (xs ys zs : List ℤ)
  → (xs +p ys) +p zs ≡ xs +p (ys +p zs)
+p-assoc [] ys zs rewrite +pLeftEmpty ys | +pLeftEmpty (ys +p zs) = refl
+p-assoc xs [] zs rewrite +pRightEmpty xs | +pLeftEmpty zs = refl
+p-assoc xs ys [] rewrite +pRightEmpty (xs +p ys) | +pRightEmpty ys = refl
+p-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  begin
    x + y + z ∷ ((xs +p ys) +p zs) 
  ≡⟨ cong ((x + y + z) ∷_) (+p-assoc xs ys zs) ⟩
     x + y + z ∷ (xs +p (ys +p zs))
   ≡⟨ cong (_∷ (xs +p (ys +p zs))) (+-assoc x y z) ⟩
     x + (y + z) ∷ (xs +p (ys +p zs))
   ∎

+p-comm : ∀ (xs ys : List ℤ)
  → xs +p ys ≡ ys +p xs
+p-comm [] ys rewrite +pLeftEmpty ys | +pRightEmpty ys = refl
+p-comm (x ∷ xs) [] = refl
+p-comm (x ∷ xs) (y ∷ ys) =
  begin
    x + y ∷ (xs +p ys)
  ≡⟨ cong ((x + y) ∷_) (+p-comm xs ys) ⟩
    x + y ∷ (ys +p xs)
  ≡⟨ cong (_∷ (ys +p xs)) (+-comm x y) ⟩
    y + x ∷ (ys +p xs)
  ∎




takeFstSplit : ∀ m xs
  → take m xs ≡ fst (splitAt m xs) 
takeFstSplit m [] rewrite splitAtEmpty m = refl
takeFstSplit zero xs rewrite takeZero xs = refl
takeFstSplit (suc n) (x ∷ xs) = refl

dropSndSplit : ∀ m xs
  → drop m xs ≡ snd (splitAt m xs)
dropSndSplit m [] rewrite splitAtEmpty m = refl
dropSndSplit zero xs rewrite dropZero xs = refl
dropSndSplit (suc n) (x ∷ xs) = refl

shiftRightDrop : ∀ (m : ℕ) (ys : List ℤ)
  → shiftRight m (snd (splitAt m ys)) ≡ shiftRight m (drop m ys)
shiftRightDrop zero xs rewrite dropZero xs = refl
shiftRightDrop m [] rewrite splitAtEmpty m = refl
shiftRightDrop (suc m) (x ∷ xs) = refl

------------------------------- split-p

split-p-new : ∀ (m : ℕ) (xs : List ℤ)
  → (m) Data.Nat.≤ (length xs)
  → xs ≡ (fst (splitAt m xs)) +p (shiftRight m (snd (splitAt m xs)))
split-p-new zero xs = λ x →
  begin
    xs
  ≡⟨ sym (+pLeftEmpty xs) ⟩
    [] +p xs
  ∎
split-p-new (ℕ.suc m) (y ∷ ys) (s≤s m≤xs) =  
  begin
    y ∷ ys
  ≡⟨ cong (_∷ ys) (sym (+-identityʳ y)) ⟩
    y + +0 ∷ ys
  ≡⟨ cong (y + +0 ∷_) ( split-p-new m ys m≤xs ) ⟩
    y + +0 ∷ (fst (splitAt m ys) +p shiftRight m (snd (splitAt m ys)))
   ≡⟨ cong (y + +0 ∷_) (cong₂ (_+p_) (sym (takeFstSplit m ys)) (shiftRightDrop m ys)) ⟩
    y + +0 ∷ (take m ys +p shiftRight m (drop m ys)) 
  ∎


split-p : ∀ (m : ℕ) (xs : List ℤ)
  →   xs ≡ (fst (splitAt m xs)) +p (shiftRight m (snd (splitAt m xs)))
split-p  m [] =
  begin
    []
  ≡⟨⟩
    [] +p [] 
  ≡⟨⟩
    (fst (take m [] , drop m [])) +p []
  ≡⟨ cong (_+p []) (cong fst (sym (splitAtEmpty m))) ⟩
    (fst ( splitAt m [])) +p []
  ≡⟨⟩
    (fst ( splitAt m [])) +p (snd (take m [] , drop m []))
  ≡⟨ cong ((fst ( splitAt m [])) +p_ ) (cong  snd (sym (splitAtEmpty m))) ⟩ 
    (fst ( splitAt m [])) +p (snd ( splitAt m []))
  ≡⟨⟩
    {!!}
    
split-p m (x ∷ xs) = {!!}






map-shiftRight-zero : ∀ (ys : List ℤ)
  → map (+0 *_) ys ≡ shiftRight (length ys) [] 
map-shiftRight-zero [] = refl
map-shiftRight-zero (y ∷ ys) =
  begin
    map (+0 *_) (y ∷ ys)
  ≡⟨⟩
     (+0 * y) ∷ map (+0 *_) ys
  ≡⟨ cong (_∷ (map (+0 *_) ys)) (*-zeroˡ y) ⟩
    +0  ∷ map (+0 *_) ys
  ≡⟨ cong (+0 ∷_) (map-shiftRight-zero ys) ⟩
    +0 ∷  shiftRight (length ys) []
  ∎


---------------------------------
-------------------  addZeroes. need to fix the conditional here
addZeroes : ∀ (m : ℕ) (xs : List ℤ)       -- if we add list zeroes to a list, and the list of zeroes |zeroes| leq |xs|,
   → (m) Data.Nat.≤ (length xs)            --xs will remain the same.
   →  shiftRight m [] +p xs ≡ xs
addZeroes  zero  xs = λ x →
  begin
    [] +p xs
   ≡⟨ +pLeftEmpty xs ⟩
     xs
   ∎
 
addZeroes (ℕ.suc m) (y ∷ ys) (s≤s m≤xs) =
  begin
    ((+0 ∷ shiftRight m []) +p (y ∷ ys))
  ≡⟨⟩
    +0 + y ∷ (shiftRight m [] +p ys)
  ≡⟨ cong (_∷ (shiftRight m [] +p ys)) (+-identityˡ y) ⟩
    y ∷ (shiftRight m [] +p ys)
  ≡⟨ cong (y ∷_) ( addZeroes m ys m≤xs ) ⟩ -- help Max
    y ∷ ys
  ∎



-- should I do this?

{-
break-out : ∀ (xs ys : List ℤ) -- xs and ys cant be empty
  →  +0 ∷ (xs *p ys) ≡ (+0 ∷ xs) *p ys 
break-out (x ∷ xs) (y ∷ ys) =
  begin
    +0 ∷ (map (_*_ x) (y ∷ ys) +p (+0 ∷ xs *p (y ∷ ys)))
  ≡⟨⟩ --+-identityʳ (x * y) |   
    +0 ∷ x * y + +0 ∷ (map (_*_ x) ys +p (xs *p (y ∷ ys)))
  ≡⟨⟩
    +0 ∷ x * y ∷ (map (_*_ x) ys +p (xs *p (y ∷ ys)))
  ≡⟨ ? ⟩
    +0 ∷ x * y ∷ (map (_*_ x) ys +p ((map (y *_) xs) +p ( +0 ∷  ys *p xs)))
  ≡⟨⟩
    ?
-}



shiftRight-two-m : ∀ (m : ℕ) (xs ys : List ℤ)
  → shiftRight m xs *p shiftRight m ys ≡ shiftRight (2 Data.Nat.* m) (xs *p ys)
shiftRight-two-m zero xs ys = refl
shiftRight-two-m (ℕ.suc m) xs ys =
  begin
    (+0 ∷ shiftRight m xs) *p (+0 ∷ shiftRight m ys)
  ≡⟨⟩
     +0 ∷ (map (+0 *_) (shiftRight m ys) +p (shiftRight m xs *p (+0 ∷ shiftRight m ys))) -- using break out here. but then no list can be empty
  ≡⟨ {!!} ⟩
    +0 ∷ (map (+0 *_) (shiftRight m ys) +p (+0 ∷ (shiftRight m xs *p shiftRight m ys)))
  ≡⟨ cong (+0 ∷_) (cong ((map (+0 *_) (shiftRight m ys)) +p_) (cong (+0 ∷_) (shiftRight-two-m m xs ys))) ⟩
     +0 ∷ (map (+0 *_) (shiftRight m ys) +p (+0 ∷ shiftRight (m Data.Nat.+ (m Data.Nat.+ zero)) (xs *p ys)))
  ≡⟨ cong (+0 ∷_) (cong (_+p (+0 ∷ shiftRight (m Data.Nat.+ (m Data.Nat.+ zero)) (xs *p ys)))  (map-shiftRight-zero (shiftRight m ys) ))  ⟩
    +0 ∷ (shiftRight (length (shiftRight m ys)) [] +p (+0 ∷ shiftRight (2 Data.Nat.* m) (xs *p ys)))
  ≡⟨ cong (+0 ∷_) ({!!} ) ⟩    --(length (shiftRight m ys)) = m + length ys
    {!!}
    


+p-assoc-two : ∀ (xs ys zs rs : List ℤ)
  → (xs +p ys) +p (zs +p rs) ≡ (xs +p zs) +p (ys +p rs)  -- ys + (rs + zs) > (ys +rs) + zs > zs + (ys + rs)
+p-assoc-two [] ys zs rs rewrite +pLeftEmpty ys | +p-comm ys (zs +p rs) | +p-assoc zs rs ys | +p-comm rs ys | +pLeftEmpty zs = refl
+p-assoc-two xs [] zs rs rewrite +pRightEmpty xs | sym (+p-assoc xs zs rs) | +pLeftEmpty rs = refl   
+p-assoc-two xs ys [] rs rewrite +pLeftEmpty rs | +p-assoc xs ys rs | +pRightEmpty xs = refl 
+p-assoc-two xs ys zs [] rewrite +pRightEmpty zs | +p-comm xs ys | +p-assoc ys xs zs | +p-comm ys (xs +p zs) | +pRightEmpty ys = refl
+p-assoc-two (x ∷ xs) (y ∷ ys) (z ∷ zs) (r ∷ rs) rewrite +p-assoc-two xs ys zs rs | +-assoc z y r = {!!} 
    
map-+p-distrib : ∀  (x : ℤ)  (xs ys : List ℤ)
  → map (x *_) xs +p map (x *_) ys ≡ map (x *_) (xs +p ys)
map-+p-distrib x [] ys rewrite +pLeftEmpty (map (x *_) ys) | +pLeftEmpty ys = refl
map-+p-distrib x xs [] rewrite  +pRightEmpty (map (x *_) xs) | +pRightEmpty xs = refl
map-+p-distrib x (y ∷ ys) (z ∷ zs) =
  begin
    x * y + x * z ∷ (map (_*_ x) ys +p map (_*_ x) zs)
  ≡⟨ cong (_∷ (map (_*_ x) ys +p map (_*_ x) zs)) (sym (*-distribˡ-+ x y z)) ⟩
    x * (y + z) ∷ (map (_*_ x) ys +p map (_*_ x) zs) 
  ≡⟨ cong ((x * (y + z)) ∷_) (map-+p-distrib x ys zs) ⟩
    x * (y + z) ∷ map (x *_) (ys +p zs)
  ∎


addZero-+p : ∀ (xs : List ℤ) -- got a more general case below.
  →  shiftRight (length xs) [] +p xs ≡ xs
addZero-+p [] = refl
addZero-+p (x ∷ xs) =
  begin
    shiftRight (length (x ∷ xs)) [] +p (x ∷ xs)
  ≡⟨⟩
    +0 + x ∷ (shiftRight (length xs) [] +p xs)
  ≡⟨ cong (_∷ (shiftRight (length xs) [] +p xs)) ( +-identityˡ x) ⟩
    x ∷ (shiftRight (length xs) [] +p xs)
  ≡⟨ cong (x ∷_) (addZero-+p xs) ⟩
    x ∷ xs
  ∎


zeroleq : ∀ (m : ℕ) 
  → (m) Data.Nat.≤ zero
  → m ≡ zero
zeroleq m = λ x → begin
                m
              ≡⟨⟩
                {!!}
--1{!!}z≤n


map-zero : ∀ (m : ℕ) (ys : List ℤ) 
  → ((shiftRight m []) *p ys) ≡ (map (+0 *_) ys +p [ +0 ])
map-zero m [] = {!!} 
map-zero m (y ∷ ys) = {!!}



shiftRight-zero-*p : ∀ (xs : List ℤ) -- how i define a list of zeroes
  →  [ +0 ] *p xs ≡ shiftRight (length xs) [] 
shiftRight-zero-*p [] = refl
shiftRight-zero-*p (x ∷ xs) =
  begin
    +0 ∷ (map (_*_ +0) xs +p [])
  ≡⟨ cong (+0 ∷_) (+pRightEmpty (map (_*_ +0) xs )) ⟩
    +0 ∷ map (_*_ +0) xs
  ≡⟨ cong (+0 ∷_) (map-shiftRight-zero xs)⟩
    +0 ∷ shiftRight (length xs) []
  ∎

map-lemma : ∀ (xs ys : List ℤ)
  → (+0 ∷ xs) *p ys ≡ map (+0 *_) ys +p (+0 ∷ (xs *p ys))
map-lemma [] ys = {!!}
map-lemma (x ∷ xs) ys = {!!}




-- this is a problem. need to defin it when ys is not empty
shiftRight-*p : ∀ (m : ℕ) (xs ys : List ℤ)
  → zero Data.Nat.< length xs
  → zero Data.Nat.< length ys
  →  shiftRight m (xs *p ys) ≡ (shiftRight m xs) *p ys
shiftRight-*p zero xs ys zero<lenXS zero<lenYS = refl
shiftRight-*p (ℕ.suc m) (x ∷ xs) (y ∷ ys) zero<lenXS zero<lenYS =
           begin
              +0 ∷ shiftRight m ((x ∷ xs) *p (y ∷ ys))
            ≡⟨ cong (+0 ∷_) (shiftRight-*p m (x ∷ xs) (y ∷ ys) zero<lenXS zero<lenYS) ⟩
              +0 ∷ ((shiftRight m (x ∷ xs)) *p (y ∷ ys) ) 
            ≡⟨ cong (+0 ∷_) (equality) ⟩ -- might be a problem with the +0 here
               (+0 ∷ (shiftRight m (x ∷ xs))) *p (y ∷ ys) 
             ∎
             where
              equality : (shiftRight m (x ∷ xs) *p (y ∷ ys)) ≡  (map (_*_ +0) ys +p (shiftRight m (x ∷ xs) *p (y ∷ ys)))
              equality = begin
                       (shiftRight m (x ∷ xs) *p (y ∷ ys))
                     ≡⟨ sym (addZeroes (length ys) (shiftRight m (x ∷ xs) *p (y ∷ ys)) {!!} ) ⟩
                       shiftRight (length ys) [] +p (shiftRight m (x ∷ xs) *p (y ∷ ys))
                     ≡⟨ cong (_+p (shiftRight m (x ∷ xs) *p (y ∷ ys))) (sym (map-shiftRight-zero ys)) ⟩
                         (map (_*_ +0) ys +p (shiftRight m (x ∷ xs) *p (y ∷ ys)))
                     ∎




shiftRight-+p : ∀ (m : ℕ) (xs ys : List ℤ)
  → shiftRight m (xs +p ys) ≡ shiftRight m xs +p shiftRight m ys
shiftRight-+p zero xs ys = refl
shiftRight-+p (ℕ.suc m) xs ys rewrite shiftRight-+p  m xs ys = refl

-- distributivity *p over +p    
*p-+p-distrib : ∀ (xs ys zs : List ℤ)
  → (xs *p ys) +p (xs *p zs) ≡ xs *p (ys +p zs)
*p-+p-distrib [] ys zs = refl
*p-+p-distrib xs [] zs =
  begin
    (xs *p []) +p (xs *p zs)
  ≡⟨ cong (_+p (xs *p zs)) (*pRightEmpty xs) ⟩
    [] +p (xs *p zs)
  ≡⟨ +pLeftEmpty (xs *p zs) ⟩
    xs *p  zs
  ≡⟨ cong (xs *p_) (sym (+pLeftEmpty zs)) ⟩
     (xs *p ([] +p zs))
    ∎
*p-+p-distrib xs ys [] =
  begin
     (xs *p ys) +p (xs *p [])
  ≡⟨ cong ((xs *p ys) +p_) (*pRightEmpty xs) ⟩
    (xs *p ys) +p []
  ≡⟨ +pRightEmpty (xs *p ys) ⟩
     xs *p  ys
  ≡⟨ cong (xs *p_) (sym (+pRightEmpty ys)) ⟩
     (xs *p (ys +p []))
    ∎
*p-+p-distrib (x ∷ xs) (y ∷ ys) (z ∷ zs) =
  begin
    ((x ∷ xs) *p (y ∷ ys)) +p ((x ∷ xs) *p (z ∷ zs))
  ≡⟨⟩
    (map (x *_) (y ∷ ys) +p (+0 ∷ xs *p (y ∷ ys))) +p (map (x *_) (z ∷ zs) +p (+0 ∷ xs *p (z ∷ zs)))
  ≡⟨ +p-assoc-two (map (x *_) (y ∷ ys)) (+0 ∷ xs *p (y ∷ ys)) (map (x *_) (z ∷ zs))  (+0 ∷ xs *p (z ∷ zs)) ⟩
    ((map (x *_) (y ∷ ys)) +p (map (x *_) (z ∷ zs))) +p ((+0 ∷ xs *p (y ∷ ys)) +p (+0 ∷ xs *p (z ∷ zs)))
  ≡⟨ cong (_+p ((+0 ∷ xs *p (y ∷ ys)) +p (+0 ∷ xs *p (z ∷ zs)))) (map-+p-distrib x (y ∷ ys) (z ∷ zs)) ⟩
    map (x *_) ((y + z) ∷ (ys +p zs)) +p ((+0 ∷ (xs *p (y ∷ ys))) +p (+0 ∷( xs *p (z ∷ zs))))
  ≡⟨⟩
    map (x *_) ((y + z) ∷ (ys +p zs)) +p (+0 ∷ ((xs *p (y ∷ ys)) +p ( xs *p (z ∷ zs))))
  ≡⟨ cong ((map (x *_) ((y + z) ∷ (ys +p zs))) +p_) (cong (+0 ∷_) (*p-+p-distrib xs (y ∷ ys) (z ∷ zs))) ⟩
    map (x *_) ((y + z) ∷ (ys +p zs)) +p (+0 ∷ (xs *p ((y ∷ ys) +p (z ∷ zs))))
  ∎


*p-lemma : ∀ (x : ℤ) (xs ys : List ℤ)
  → (x ∷ xs) *p ys ≡ (map (x *_) ys) +p ( +0 ∷  xs *p ys)
*p-lemma x [] ys =
  begin
    [ x ] *p ys
  ≡⟨ *p-map-left-single x ys ⟩  
    map (x *_) ys
 --≡⟨ sym (addZeroes 1 (map (x *_) ys)) ⟩
 ≡⟨ {!!} ⟩
    (shiftRight 1 []) +p (map (x *_) ys) 
  ≡⟨⟩
    {!!}


*p-comm : ∀ (xs ys : List ℤ)
  → xs *p ys ≡ ys *p xs
*p-comm [] ys rewrite *pRightEmpty ys = refl
*p-comm xs [] rewrite *pRightEmpty xs = refl
*p-comm (x ∷ xs) ys = 
  begin
    (x ∷ xs) *p ys
  ≡⟨⟩
    {!!}

*p-+p-distrib-four : ∀ (xs ys zs rs : List ℤ)
  → ((xs +p ys) *p (zs +p rs)) ≡ ((((xs *p zs) +p (xs *p rs)) +p (ys *p zs)) +p (ys *p rs))
*p-+p-distrib-four [] ys zs rs rewrite +pLeftEmpty ys | sym ( *p-+p-distrib ys zs rs) | +pLeftEmpty (ys *p zs) = refl
*p-+p-distrib-four xs [] zs rs rewrite +pRightEmpty xs | sym (*p-+p-distrib xs zs rs) | +pRightEmpty ((xs *p zs) +p (xs *p rs)) | +pRightEmpty  ((xs *p zs) +p (xs *p rs)) = refl 
*p-+p-distrib-four xs ys [] rs rewrite sym (*p-+p-distrib (xs +p ys) [] rs) = {!!} 
*p-+p-distrib-four xs ys zs rs = {!!}



-------------------

ad+bc : ∀ (xs ys zs rs : List ℤ)
  → (((xs +p ys) *p (zs +p rs)) -p (xs *p zs)) -p (ys *p rs) ≡ (xs *p rs) +p (ys *p zs)
ad+bc [] ys zs rs rewrite +pLeftEmpty ys | +pRightEmpty (ys *p (zs +p rs)) | sym (*p-+p-distrib  ys zs rs) | +p-assoc (ys *p zs) (ys *p rs) (negPoly (ys *p rs))   | negPoly-lemma (ys *p rs) = {!!}   


ismul' : ∀ (n : ℕ) (xs ys : List ℤ)
  → xs *p ys ≡ karatsuba' n xs ys  
ismul' zero xs ys = refl
ismul' (suc n) xs ys with (((length xs / 2) ⊓ (length ys / 2)) ≤ᵇ' 2)
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
                           let ad_plus_bc = ((karatsuba' n a_plus_b c_plus_d) -p ac) -p bd in
                           xs *p ys
                         ≡⟨ cong₂ (_*p_) (split-p-new  m xs) (split-p-new  m ys) ⟩  --length conditional missing
                           (b +p shiftRight m a) *p (d +p shiftRight m c)
                       
                         ≡⟨ *p-+p-distrib-four  b (shiftRight m a) d (shiftRight m c) ⟩   -- distrib 3 done. but haven´t finished 4
                          (((b *p d) +p (b *p (shiftRight m c))) +p ((shiftRight m a) *p d)) +p (shiftRight m a *p shiftRight m c)
                          
                         ≡⟨ cong (_+p (shiftRight m a *p shiftRight m c)) (+p-assoc (b *p d) (b *p (shiftRight m c)) ((shiftRight m a) *p d) ) ⟩ -- done
                          ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p (shiftRight m a *p shiftRight m c)
                          
                         ≡⟨ cong (((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p_) (shiftRight-two-m m a c) ⟩  -- shiftRight-two-m not done. wan´t to break out x for lemma
                           ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p ((shiftRight (2 *ℕ m) (a *p c)))          -- shiftRight-+p done. shiftRight-*p not done, need conditional for length . *p-comm would be nice
                         ≡⟨ {!!} ⟩                                                                                                                                                                                                           -- ad+bc, just started
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd ∎
                           
