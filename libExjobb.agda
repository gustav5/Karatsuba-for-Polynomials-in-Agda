import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _⊓_; _⊔_ ;z≤n; s≤s;z<s;s<s) renaming( _*_ to _*ℕ_ ;_+_ to _+ℕ_;_<?_ to _<?ℕ_; _≤?_ to  _≤?ℕ_; _≤_ to _≤ℕ_; _<_ to _<ℕ_;_≥_ to  _≥ℕ_ )
open import Data.Nat.Base using (_/_)
open import Data.Nat.Properties using (⊓-zeroʳ; m≤n⇒m⊓n≡m )
open import Data.Nat.DivMod
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer.Base hiding (_⊓_;_/_;_⊔_) 
open import Data.Integer.Properties  
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Level using (Level)

----- Library

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


-- functions
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  ℕ.suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

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


if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y


infix 4 _≤ᵇ'_

_≤ᵇ'_ : ℕ → ℕ → Bool
zero ≤ᵇ' n       =  true
suc m ≤ᵇ' zero   =  false
suc m ≤ᵇ' suc n  =  m ≤ᵇ' n

a : List ℤ
a = [ + 2 ]

b : List ℤ
b = [ + 1 , + 2   ]



--proofs for functions
----------------------------------
-------------- working help functions


+-rearrange : ∀ (m n p q : ℤ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q rewrite +-assoc m n (p + q) | (sym (+-assoc n p q)) | sym (+-assoc m (n + p) q) = refl

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

addOne : ∀ (x : ℤ) (xs : List ℤ)
  →  x ∷ xs ≡ [ x ] +p (+0 ∷ xs) 
addOne x [] rewrite +-identityʳ x = refl
addOne x (y ∷ ys) rewrite +-identityʳ x = refl

takeFstSplit : ∀ m xs
  → take m xs ≡ Pair.fst (splitAt m xs) 
takeFstSplit m [] rewrite splitAtEmpty m = refl
takeFstSplit zero xs rewrite takeZero xs = refl
takeFstSplit (suc n) (x ∷ xs) = refl

dropSndSplit : ∀ m xs
  → drop m xs ≡ Pair.snd (splitAt m xs)
dropSndSplit m [] rewrite splitAtEmpty m = refl
dropSndSplit zero xs rewrite dropZero xs = refl
dropSndSplit (suc n) (x ∷ xs) = refl

shiftRightDrop : ∀ (m : ℕ) (ys : List ℤ)
  → shiftRight m (Pair.snd (splitAt m ys)) ≡ shiftRight m (drop m ys)
shiftRightDrop zero xs rewrite dropZero xs = refl
shiftRightDrop m [] rewrite splitAtEmpty m = refl
shiftRightDrop (suc m) (x ∷ xs) = refl

--properties of +p

--identity
+pRightEmpty : ∀ (xs : List ℤ)
  → xs +p [] ≡ xs
+pRightEmpty [] = refl
+pRightEmpty (x ∷ xs) = refl

+pLeftEmpty : ∀ (xs : List ℤ)
  → [] +p xs ≡ xs
+pLeftEmpty []  = refl
+pLeftEmpty (x ∷ xs) = refl


--associativity
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

--commutativity
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

--rearrange
+p-rearrange : ∀ (xs ys zs rs : List ℤ)
  → (xs +p ys) +p (zs +p rs) ≡ (xs +p (ys +p zs)) +p rs
+p-rearrange [] ys zs rs rewrite +pLeftEmpty ys | sym (+p-assoc ys zs rs) | +pLeftEmpty (ys +p zs) = refl 
+p-rearrange xs [] zs rs rewrite +pRightEmpty xs | sym (+p-assoc xs zs rs) | +pLeftEmpty zs = refl
+p-rearrange xs ys [] rs rewrite +pLeftEmpty rs | +pRightEmpty ys = refl
+p-rearrange xs ys zs [] rewrite +pRightEmpty zs | +p-assoc xs ys zs   | +pRightEmpty (xs +p (ys +p zs)) = refl 
+p-rearrange (x ∷ xs) (y ∷ ys) (z ∷ zs) (r ∷ rs) rewrite +-rearrange x y z r | +p-rearrange xs ys zs rs = refl   

--associativty for four variables
+p-assoc-two : ∀ (xs ys zs rs : List ℤ)
  → (xs +p ys) +p (zs +p rs) ≡ (xs +p zs) +p (ys +p rs)  -- ys + (rs + zs) > (ys +rs) + zs > zs + (ys + rs)
+p-assoc-two [] ys zs rs rewrite +pLeftEmpty ys | +p-comm ys (zs +p rs) | +p-assoc zs rs ys | +p-comm rs ys | +pLeftEmpty zs = refl
+p-assoc-two xs [] zs rs rewrite +pRightEmpty xs | sym (+p-assoc xs zs rs) | +pLeftEmpty rs = refl   
+p-assoc-two xs ys [] rs rewrite +pLeftEmpty rs | +p-assoc xs ys rs | +pRightEmpty xs = refl 
+p-assoc-two xs ys zs [] rewrite +pRightEmpty zs | +p-comm xs ys | +p-assoc ys xs zs | +p-comm ys (xs +p zs) | +pRightEmpty ys = refl
+p-assoc-two ( x ∷ xs) (y ∷ ys) (z ∷ zs) (r ∷ rs)  rewrite +p-assoc-two xs ys zs rs | +-rearrange x y z r | +-comm y z | sym (+-rearrange x z y r) = refl 

map-+p-dist-two : ∀  (x y : ℤ)  (zs : List ℤ)
  → (map (x *_) zs) +p (map (y *_) zs) ≡ map ((x + y) *_) zs
map-+p-dist-two x y []  = refl
map-+p-dist-two x y (z ∷ zs) =
  begin
    x * z + y * z ∷ (map (_*_ x) zs +p map (_*_ y) zs)
  ≡⟨ cong (_∷ (map (_*_ x) zs +p map (_*_ y) zs)) (sym (*-distribʳ-+ z x y)) ⟩
    (x + y) * z ∷ (map (_*_ x) zs +p map (_*_ y) zs)
  ≡⟨ cong ((x + y) * z ∷_) (map-+p-dist-two x y zs) ⟩
    (x + y) * z ∷ map (_*_ (x + y)) zs
  ∎
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

addZeroes : ∀ (m : ℕ) (xs : List ℤ)       
   → (m) ≤ℕ (length xs)          
   →  shiftRight m [] +p xs ≡ xs
addZeroes  zero  xs m≤xs = 
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
  ≡⟨ cong (y ∷_) ( addZeroes m ys m≤xs ) ⟩ 
    y ∷ ys
  ∎


negPoly-lemma : ∀ (xs : List ℤ)
  → xs +p (negPoly xs) ≡ shiftRight (length xs) []
negPoly-lemma [] = refl
negPoly-lemma (x ∷ xs) =
  begin
     x + - x ∷ (xs +p negPoly xs)  --help max
  ≡⟨ cong (_∷ (xs +p negPoly xs)) (+-inverseʳ x) ⟩
    +0 ∷ (xs +p negPoly xs)
  ≡⟨ cong (+0 ∷_) (negPoly-lemma xs) ⟩
    +0 ∷ shiftRight (length xs) []
  ∎


-- split

split-p-new : ∀ (m : ℕ) (xs : List ℤ)
  → (m) Data.Nat.≤ (length xs)
  → xs ≡ (Pair.fst (splitAt m xs)) +p (shiftRight m (Pair.snd (splitAt m xs)))
split-p-new zero xs m≤xs = 
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
    y + +0 ∷ (Pair.fst (splitAt m ys) +p shiftRight m (Pair.snd (splitAt m ys)))
   ≡⟨ cong (y + +0 ∷_) (cong₂ (_+p_) (sym (takeFstSplit m ys)) (shiftRightDrop m ys)) ⟩
    y + +0 ∷ (take m ys +p shiftRight m (drop m ys)) 
  ∎

--properties of *p

--identity
*pRightEmpty : ∀ (xs : List ℤ)
  → xs *p [] ≡ []
*pRightEmpty []  = refl
*pRightEmpty (x ∷ xs) = refl

*pLeftEmpty : ∀ (xs : List ℤ)
  → [] *p xs ≡ []
*pLeftEmpty []  = refl
*pLeftEmpty (x ∷ xs) = refl

*p-map-left-single : ∀ (x : ℤ) (ys : List ℤ)
  → [ x ] *p ys ≡ map (x *_) ys
*p-map-left-single x [] = refl
*p-map-left-single x (y ∷ ys) =
  begin
    [ x ] *p (y ∷ ys)
  ≡⟨⟩
    (x ∷ []) *p (y ∷ ys)
  ≡⟨⟩
    (map (x *_) (y ∷ ys)) +p ( +0 ∷ [] *p (y ∷ ys))
  ≡⟨⟩
    (x * y ∷ map (x *_) ys) +p [ +0 ] 
  ≡⟨⟩
    x * y + +0 ∷ (map (x *_) ys) +p []
  ≡⟨ cong ((x * y + +0) ∷_) (+pRightEmpty (map (x *_) ys)) ⟩
    x * y + +0 ∷ map (x *_) ys
  ≡⟨ cong ( _∷ map (x *_) ys) (+-identityʳ (x * y)) ⟩
   x * y ∷ map (x *_) ys
  ∎

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

*p-+p-distrib-l : ∀ (xs ys zs : List ℤ)
  → (xs *p ys) +p (xs *p zs) ≡ xs *p (ys +p zs)
*p-+p-distrib-l [] ys zs = refl
*p-+p-distrib-l xs [] zs rewrite *pRightEmpty xs | +pLeftEmpty (xs *p zs) | +pLeftEmpty zs = refl 
*p-+p-distrib-l xs ys [] rewrite *pRightEmpty xs | +pRightEmpty (xs *p ys) | +pRightEmpty ys = refl  
*p-+p-distrib-l (x ∷ xs) (y ∷ ys) (z ∷ zs) =
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
  ≡⟨ cong ((map (x *_) ((y + z) ∷ (ys +p zs))) +p_) (cong (+0 ∷_) (*p-+p-distrib-l xs (y ∷ ys) (z ∷ zs))) ⟩
    map (x *_) ((y + z) ∷ (ys +p zs)) +p (+0 ∷ (xs *p ((y ∷ ys) +p (z ∷ zs))))
  ∎

*p-+p-distrib-r : ∀ (xs ys zs : List ℤ)
  →  (xs *p zs) +p (ys *p zs) ≡ (xs +p ys) *p zs 
*p-+p-distrib-r [] ys zs  = -- rewrite +pLeftEmpty (ys *p zs) |  sym ( +pLeftEmpty ys ) = {!!}  
 begin
    [] +p (ys  *p zs) 
  ≡⟨ +pLeftEmpty (ys *p zs) ⟩
    ys *p zs
  ≡⟨ cong (_*p zs) (sym (+pLeftEmpty ys)) ⟩
    ([] +p ys) *p zs
  ∎
*p-+p-distrib-r xs [] zs = 
  begin
     ((xs *p zs) +p []) 
   ≡⟨  +pRightEmpty (xs *p zs) ⟩
    xs *p zs
  ≡⟨ cong (_*p zs) (sym (+pRightEmpty xs)) ⟩
    ((xs +p []) *p zs)
  ∎
    
*p-+p-distrib-r xs ys [] = --  rewrite *pRightEmpty (xs +p ys) | *pRightEmpty xs = 
  begin
    ((xs *p []) +p (ys *p []))
  ≡⟨ cong₂ (_+p_) (*pRightEmpty xs) (*pRightEmpty ys) ⟩
    []
  ≡⟨ sym (*pRightEmpty (xs +p ys)) ⟩
    ((xs +p ys) *p [])
  ∎

*p-+p-distrib-r  (x ∷ xs) (y ∷ ys) (z ∷ zs)=
  begin
    (map (x *_) (z ∷ zs) +p (+0 ∷ xs *p (z ∷ zs))) +p (map (y *_) (z ∷ zs) +p (+0 ∷ ys *p (z ∷ zs)))
  ≡⟨ +p-assoc-two (map (x *_) (z ∷ zs)) (+0 ∷ xs *p (z ∷ zs)) (map (y *_) (z ∷ zs))  (+0 ∷ ys *p (z ∷ zs)) ⟩
   ((map (x *_) (z ∷ zs)) +p (map (y *_) (z ∷ zs))) +p ((+0 ∷ xs *p (z ∷ zs)) +p (+0 ∷ ys *p (z ∷ zs)))
  ≡⟨ cong (_+p ((+0 ∷ xs *p (z ∷ zs)) +p (+0 ∷ ys *p (z ∷ zs)))) (map-+p-dist-two  x y (z ∷ zs)) ⟩
    (x + y) * z + +0 ∷ (map (_*_ (x + y)) zs +p ((xs *p (z ∷ zs)) +p (ys *p (z ∷ zs))))
  ≡⟨ cong ( (x + y) * z + +0 ∷_) (cong (map (_*_ (x + y)) zs +p_) (*p-+p-distrib-r xs ys (z ∷ zs))) ⟩
     (x + y) * z + +0 ∷ (map (_*_ (x + y)) zs +p ((xs +p ys) *p (z ∷ zs)))
   ∎


--properties of length

lengthseven : ∀ (xs ys : List ℤ)
  → length (xs +p ys) ≡ length xs ⊔ length ys
lengthseven [] ys rewrite +pLeftEmpty ys = refl
lengthseven xs [] rewrite +pRightEmpty xs | Data.Nat.Properties.⊔-identityʳ (length xs) = refl  
lengthseven (x ∷ xs) (y ∷ ys) rewrite lengthseven xs ys = refl  


length-map : ∀ (x : ℤ) (xs : List ℤ)
  → length xs ≡ length (map (x *_) xs)
length-map x [] = refl
length-map x (y ∷ ys) rewrite length-map x ys = refl  




--properties of shiftRight

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



shiftRight-shiftRight : ∀ (m n : ℕ) (xs  : List ℤ)
  → shiftRight m (shiftRight n xs) ≡ shiftRight (m +ℕ n) xs
shiftRight-shiftRight zero n xs = refl
shiftRight-shiftRight (ℕ.suc m) n xs rewrite shiftRight-shiftRight m n xs = refl 


shiftRight-+p : ∀ (m : ℕ) (xs ys : List ℤ)
  → shiftRight m (xs +p ys) ≡ shiftRight m xs +p shiftRight m ys
shiftRight-+p zero xs ys = refl
shiftRight-+p (ℕ.suc m) xs ys rewrite shiftRight-+p  m xs ys = refl


shiftRight-len : ∀ (m : ℕ) 
  → length (shiftRight m []) ≡ m
shiftRight-len zero = refl
shiftRight-len (ℕ.suc m) rewrite shiftRight-len m = refl 
  
shiftRight-list-len : ∀ (m : ℕ) (xs : List ℤ)
  → length (shiftRight m xs) ≡ length xs +ℕ m 
shiftRight-list-len zero xs  rewrite Data.Nat.Properties.+-identityʳ (length xs) = refl   
shiftRight-list-len (ℕ.suc m) xs =  
  begin
    ℕ.suc (length (shiftRight m xs)) --length (shiftRight m xs)
  ≡⟨ cong ℕ.suc (shiftRight-list-len m xs) ⟩
    ℕ.suc (length xs +ℕ m)
  ≡⟨ cong ℕ.suc (Data.Nat.Properties.+-comm (length xs) m) ⟩
    ℕ.suc (m +ℕ length xs)
  ≡⟨⟩
    ℕ.suc m +ℕ length xs
  ≡⟨ Data.Nat.Properties.+-comm (ℕ.suc m) (length xs) ⟩
    length xs +ℕ ℕ.suc m
  ∎
