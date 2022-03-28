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

shiftRightEmpty : ∀ (n : ℕ)
  → shiftRight n [] ≡ []
shiftRightEmpty n = refl


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
  ≡⟨ {!!} ⟩
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
   




--------------------------
---------------   in progress



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


---------------------------------
-------------------  proof in progress

addOne : ∀ (x : ℤ) (xs : List ℤ)
  →  x ∷ xs ≡ [ x ] +p (+0 ∷ xs) 
addOne x [] rewrite +-identityʳ x = refl
addOne x (y ∷ ys) rewrite +-identityʳ x = refl

--(x ∷ xs) +p (y ∷ ys) ≡ [ x + y ] ∷ (xs +p ys)
--x ∷ xs +p ys ≡ ([ x ] +p ((+0 ∷ xs) +p ys) ≡



test-lemma : ∀ (x y : ℤ) (xs ys : List ℤ)
  → [ x + y ] +p ((+0 ∷ xs) +p (+0 ∷ ys)) ≡ (x ∷ xs) +p (y ∷ ys)
test-lemma x y xs ys =
  begin
    [ x + y ] +p ((+0 ∷ xs) +p (+0 ∷ ys))
  ≡⟨⟩
    {!!}
  --  ([ x ] +p [ y ]) +p ((+0 ∷ xs) +p (+0 ∷ ys))
  --≡⟨⟩
  --  (([ x ] +p [ y ]) +p (+0 ∷ ys)) +p (+0 ∷ xs))
  --≡⟨⟩
  
--(x ∷ xs) +p (y ∷ ys) = x + y ∷ (xs +p ys)
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
test-two : ∀ (x : ℤ) (xs : List ℤ)
  → x ∷ xs ≡ [ x ] +p (+0 ∷ xs)
test-two x [] =
  begin
    x ∷ []
  ≡⟨ cong (_∷ []) (sym (+-identityʳ x)) ⟩
    [ x + +0 ]
  ≡⟨⟩
    [ x ] +p [ +0 ]
  ∎
test-two x (y ∷ ys) rewrite +-identityʳ x = refl
--[] +p [] = []
--xs +p [] = xs
--[] +p ys = ys
--(x ∷ xs) +p (y ∷ ys) = x + y ∷ (xs +p ys) 

+p-assoc : ∀ (xs ys zs : List ℤ)
  → ( xs +p ys ) +p zs ≡ xs +p ( ys +p zs)
+p-assoc [] ys zs =
  begin
    ( [] +p ys ) +p zs
  ≡⟨ cong (_+p zs) (+pLeftEmpty ys ) ⟩
    (ys +p zs)
  ≡⟨ sym (+pLeftEmpty (ys +p zs)) ⟩
    [] +p (ys +p zs)
  ∎ 
+p-assoc (x ∷ xs) ys zs =
  begin
    (( x ∷ xs) +p ys) +p zs
  ≡⟨ cong (_+p zs) (cong (_+p ys) (test-two x xs)) ⟩
    (([ x ] +p (+0 ∷ xs)) +p ys) +p zs 
  ≡⟨ cong (_+p zs) (+p-assoc [ x ] (+0 ∷ xs) ys ) ⟩
    ([ x ] +p ((+0 ∷ xs) +p ys)) +p zs     
  ≡⟨ +p-assoc [ x ] ((+0 ∷ xs) +p ys) zs ⟩
    [ x ] +p (((+0 ∷ xs) +p ys) +p zs)
  ≡⟨ cong ([ x ] +p_) ( +p-assoc (+0 ∷ xs) ys zs) ⟩
    [ x ] +p ((+0 ∷ xs) +p ( ys +p zs))
  ≡⟨ sym (+p-assoc [ x ] (+0 ∷ xs) ( ys +p zs)) ⟩
    ([ x ] +p (+0 ∷ xs)) +p (ys +p zs)
  ≡⟨ cong (_+p (ys +p zs)) ( sym (test-two x xs)) ⟩
    (x ∷ xs) +p (ys +p zs)
  ∎

-- +p-assoc (x ∷ xs) (y ∷ ys) zs rewrite addOne x xs | addOne y ys | +p-assoc xs ys zs ≡ refl

--    [ x + y ] +p (+0 ∷ (xs +p ys)) +p zs
--  ≡⟨ ? ⟩
--    [ x + y ] +p ((+0 ∷ xs) +p (+0 ∷ ys)) +p zs
--  ≡⟨ ? ⟩
--    [ x + y ] +p ((+0 ∷ xs) +p ((+0 ∷ ys) +p zs))
--  ≡⟨ ? ⟩
--    [ x + y ] +p (+0 ∷ xs) +p (+0 ∷ ys) +p zs
--  ≡⟨ ? ⟩
--    
--   ((x ∷ xs) +p ((y ∷ ys) +p zs))
-- ∎
    
*p-map : ∀ (x y : ℤ) (xs ys : List ℤ)
  → (x ∷ xs) *p (y ∷ ys) ≡ (map (x *_) ys) +p (+0 ∷ (xs *p ys))
*p-map x y [] ys =
  begin
    {!!}
--    x * y ∷ map (x *_) ys
--  ≡⟨⟩
--   map (x *_) (y ∷ ys)
-- ≡⟨⟩
   {!!}
--  ≡⟨ {!!} ⟩ -- plus 0
--   map (x *_) ys +p [ +0 ]
--  ∎


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

--addOne : ∀ (x : ℤ) (xs : List ℤ)
--  →  x ∷ xs ≡ [ x ] +p (+0 ∷ xs) 
*p-comm : ∀ (xs ys : List ℤ) 
  → xs *p ys ≡  ys *p xs
*p-comm [] ys rewrite *pRightEmpty ys = refl
*p-comm (x ∷ xs) ys =
  begin
    (x ∷ xs) *p ys
  ≡⟨ cong (_*p ys) (addOne x xs) ⟩
 --   ([ x ] +p (+0 ∷ xs)) *p
 
    {!!}


--_*p_ (x ∷ xs) ys = (map (x *_) ys) +p ( +0 ∷  xs *p ys)
--(x ∷ xs) +p (y ∷ ys) ≡ [ x + y ] ∷ (xs +p ys)
--x ∷ xs +p ys ≡ ([ x ] +p ((+0 ∷ xs) +p ys) ≡
*p-distrib : ∀ (xs ys zs : List ℤ)
  → xs *p (ys +p zs) ≡ (xs *p ys) +p (xs *p zs)
*p-distrib xs [] zs =
  begin
    (xs *p ([] +p zs))
  ≡⟨ cong (xs *p_) ( +pLeftEmpty zs) ⟩
    (xs *p zs)
  ≡⟨ sym (+pLeftEmpty (xs *p zs)) ⟩
    [] +p (xs *p zs)   
  ≡⟨ cong (_+p (xs *p zs)) (sym (*pRightEmpty xs)) ⟩
    ((xs *p []) +p (xs *p zs))
  ∎
-- (map (x *_) ys) +p ( +0 ∷  xs *p ys)
--*p-distrib xs (y ∷ ys) zs =
--  begin
--   ((x ∷ xs) *p (ys +p zs))
--  ≡⟨ {!!} ⟩
--   (map (x *_) ys) +p ( +0 ∷  xs *p ys)
--  ≡⟨ ? ⟩
 --   [x * (head y)] ∷ map (x *_) ys +p ( +0 ∷  xs *p ys)
  --  [x * (head y)] +p (+0 ∷ map (x *_) ys) +p ( +0 ∷  xs *p ys)
 -- ∎


distribBig : ∀ (xs ys zs rs : List ℤ)
  → (xs +p ys) *p (zs +p rs) ≡ (xs *p zs) +p ((xs *p rs) +p ((ys *p zs) +p (ys *p rs)))
distribBig [] ys zs rs =
  begin
    ([] +p ys) *p (zs +p rs)
  ≡⟨ cong (_*p (zs +p rs)) (+pLeftEmpty ys) ⟩
    ys *p (zs +p rs)
  ≡⟨ *p-distrib ys zs rs ⟩
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
                         ≡⟨ cong₂ mulPoly (split-p m xs) (split-p m ys) ⟩
                           mulPoly (b +p shiftRight m a) (d +p shiftRight m c)
                         ≡⟨ {!!} ⟩
                           (((mulPoly (shiftRight m a) (shiftRight m c)) +p (mulPoly (shiftRight m a) d)) +p  (mulPoly b (shiftRight m c))) +p (mulPoly b d)
                         ≡⟨ {!!} ⟩ --- försök på den här på måndag
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd ∎
                           
