import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Nat renaming( _*_ to _*ℕ_)   --using (ℕ; zero; suc; _⊓_; _⊔_ ;z≤n; s≤s;z<s;s<s) renaming( _*_ to _*ℕ_ ;_+_ to _+ℕ_;_<?_ to _<?ℕ_; _≤?_ to  _≤?ℕ_; _≤_ to _≤ℕ_; _<_ to _<ℕ_;_≥_ to  _≥ℕ_ ) hiding (-)
open import Data.Nat.Properties renaming(*-comm to *-commℕ)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer  using (ℤ;+0;_*_) renaming (_+_ to _+ℤ_; -_ to -i_) 
open import Data.Integer.Properties hiding(_≤?_;≰⇒>;_<?_;m≤n⇒m⊔n≡n;≤-reflexive;<⇒≤;m≤n⇒m⊓n≡m;m≤m+n ;≤-trans) renaming (*-zeroʳ to *-zeroʳℤ;*-zeroˡ to *-zeroˡℤ;+-inverseʳ to +-inverseʳℤ; +-identityʳ to +-identityʳℤ;+-identityˡ to +-identityˡℤ;+-comm to +-commℤ;*-distribʳ-+ to *-distribʳ-+ℤ;*-distribˡ-+ to *-distribˡ-+ℤ;≤-refl to ≤-reflℤ;+-assoc to +-assocℤ)
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
(x ∷ xs) +p (y ∷ ys) = x +ℤ y ∷ (xs +p ys) 

_*p_ : List ℤ → List ℤ → List ℤ
_*p_ [] ys = []
_*p_ xs [] = []
_*p_ (x ∷ xs) ys = (map (x *_) ys) +p ( +0 ∷  xs *p ys)

negPoly : List ℤ → List ℤ
negPoly [] = []
negPoly (x ∷ xs) = (-i x) ∷ negPoly xs

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

-- a : List ℤ
-- a = [ + 2 ]

-- b : List ℤ
-- b = [ + 1 , + 2   ]



--proofs for functions
----------------------------------
-------------- working help functions


+-rearrange : ∀ (m n p q : ℤ) → (m +ℤ n) +ℤ (p +ℤ q) ≡ m +ℤ (n +ℤ p) +ℤ q
+-rearrange m n p q rewrite +-assocℤ m n (p +ℤ q) | (sym (+-assocℤ n p q)) | sym (+-assocℤ m (n +ℤ p) q) = refl

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
addOne x [] rewrite +-identityʳℤ x = refl
addOne x (y ∷ ys) rewrite +-identityʳℤ x = refl

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
    x +ℤ y +ℤ z ∷ ((xs +p ys) +p zs) 
  ≡⟨ cong ((x +ℤ y +ℤ z) ∷_) (+p-assoc xs ys zs) ⟩
     x +ℤ y +ℤ z ∷ (xs +p (ys +p zs))
   ≡⟨ cong (_∷ (xs +p (ys +p zs))) (+-assocℤ x y z) ⟩
     x +ℤ (y +ℤ z) ∷ (xs +p (ys +p zs))
   ∎

--commutativity
+p-comm : ∀ (xs ys : List ℤ)
  → xs +p ys ≡ ys +p xs
+p-comm [] ys rewrite +pLeftEmpty ys | +pRightEmpty ys = refl
+p-comm (x ∷ xs) [] = refl
+p-comm (x ∷ xs) (y ∷ ys) =
  begin
    x +ℤ y ∷ (xs +p ys)
  ≡⟨ cong ((x +ℤ y) ∷_) (+p-comm xs ys) ⟩
    x +ℤ y ∷ (ys +p xs)
  ≡⟨ cong (_∷ (ys +p xs)) (+-commℤ x y) ⟩
    y +ℤ x ∷ (ys +p xs)
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
+p-assoc-two ( x ∷ xs) (y ∷ ys) (z ∷ zs) (r ∷ rs)  rewrite +p-assoc-two xs ys zs rs | +-rearrange x y z r | +-commℤ y z | sym (+-rearrange x z y r) = refl 

map-+p-dist-two : ∀  (x y : ℤ)  (zs : List ℤ)
  → (map (x *_) zs) +p (map (y *_) zs) ≡ map ((x +ℤ y) *_) zs
map-+p-dist-two x y []  = refl
map-+p-dist-two x y (z ∷ zs) =
  begin
    x * z +ℤ y * z ∷ (map (_*_ x) zs +p map (_*_ y) zs)
  ≡⟨ cong (_∷ (map (_*_ x) zs +p map (_*_ y) zs)) (sym (*-distribʳ-+ℤ z x y)) ⟩
    (x +ℤ y) * z ∷ (map (_*_ x) zs +p map (_*_ y) zs)
  ≡⟨ cong ((x +ℤ y) * z ∷_) (map-+p-dist-two x y zs) ⟩
    (x +ℤ y) * z ∷ map (_*_ (x +ℤ y)) zs
  ∎
map-+p-distrib : ∀  (x : ℤ)  (xs ys : List ℤ)
  → map (x *_) xs +p map (x *_) ys ≡ map (x *_) (xs +p ys)
map-+p-distrib x [] ys rewrite +pLeftEmpty (map (x *_) ys) | +pLeftEmpty ys = refl
map-+p-distrib x xs [] rewrite  +pRightEmpty (map (x *_) xs) | +pRightEmpty xs = refl
map-+p-distrib x (y ∷ ys) (z ∷ zs) =
  begin
    x * y +ℤ x * z ∷ (map (_*_ x) ys +p map (_*_ x) zs)
  ≡⟨ cong (_∷ (map (_*_ x) ys +p map (_*_ x) zs)) (sym (*-distribˡ-+ℤ x y z)) ⟩
    x * (y +ℤ z) ∷ (map (_*_ x) ys +p map (_*_ x) zs) 
  ≡⟨ cong ((x * (y +ℤ z)) ∷_) (map-+p-distrib x ys zs) ⟩
    x * (y +ℤ z) ∷ map (x *_) (ys +p zs)
  ∎

addZeroes : ∀ (m : ℕ) (xs : List ℤ)       
   → (m) ≤ (length xs)          
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
    +0 +ℤ y ∷ (shiftRight m [] +p ys)
  ≡⟨ cong (_∷ (shiftRight m [] +p ys)) (+-identityˡℤ y) ⟩
    y ∷ (shiftRight m [] +p ys)
  ≡⟨ cong (y ∷_) ( addZeroes m ys m≤xs ) ⟩ 
    y ∷ ys
  ∎


negPoly-lemma : ∀ (xs : List ℤ)
  → xs +p (negPoly xs) ≡ shiftRight (length xs) []
negPoly-lemma [] = refl
negPoly-lemma (x ∷ xs) =
  begin
     x +ℤ -i x ∷ (xs +p negPoly xs)  --help max
  ≡⟨ cong (_∷ (xs +p negPoly xs)) (+-inverseʳℤ x) ⟩
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
  ≡⟨ cong (_∷ ys) (sym (+-identityʳℤ y)) ⟩
    y +ℤ +0 ∷ ys
  ≡⟨ cong (y +ℤ +0 ∷_) ( split-p-new m ys m≤xs ) ⟩
    y +ℤ +0 ∷ (Pair.fst (splitAt m ys) +p shiftRight m (Pair.snd (splitAt m ys)))
   ≡⟨ cong (y +ℤ +0 ∷_) (cong₂ (_+p_) (sym (takeFstSplit m ys)) (shiftRightDrop m ys)) ⟩
    y +ℤ +0 ∷ (take m ys +p shiftRight m (drop m ys)) 
  ∎

  
split-p : ∀ (m : ℕ) (xs : List ℤ)
  → (m) ≤ (length xs)
  → xs ≡ take m xs +p (shiftRight m (drop m xs))
split-p zero xs m≤xs rewrite takeZero xs | dropZero xs | +pLeftEmpty xs = refl
split-p (ℕ.suc m) (y ∷ ys) (s≤s m≤xs) =
  begin
    y ∷ ys
  ≡⟨ cong (_∷ ys) (sym (+-identityʳℤ y)) ⟩
    y +ℤ +0 ∷ ys
  ≡⟨ cong (y +ℤ +0 ∷_) ( split-p m ys m≤xs ) ⟩
    y +ℤ +0 ∷ (take m ys +p shiftRight m (drop m ys))
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
    x * y +ℤ +0 ∷ (map (x *_) ys) +p []
  ≡⟨ cong ((x * y +ℤ +0) ∷_) (+pRightEmpty (map (x *_) ys)) ⟩
    x * y +ℤ +0 ∷ map (x *_) ys
  ≡⟨ cong ( _∷ map (x *_) ys) (+-identityʳℤ (x * y)) ⟩
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
  ≡⟨ cong (_∷ (map (+0 *_) ys)) (*-zeroˡℤ y) ⟩
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
    map (x *_) ((y +ℤ z) ∷ (ys +p zs)) +p ((+0 ∷ (xs *p (y ∷ ys))) +p (+0 ∷( xs *p (z ∷ zs))))
  ≡⟨⟩
    map (x *_) ((y +ℤ z) ∷ (ys +p zs)) +p (+0 ∷ ((xs *p (y ∷ ys)) +p ( xs *p (z ∷ zs))))
  ≡⟨ cong ((map (x *_) ((y +ℤ z) ∷ (ys +p zs))) +p_) (cong (+0 ∷_) (*p-+p-distrib-l xs (y ∷ ys) (z ∷ zs))) ⟩
    map (x *_) ((y +ℤ z) ∷ (ys +p zs)) +p (+0 ∷ (xs *p ((y ∷ ys) +p (z ∷ zs))))
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
    (x +ℤ y) * z +ℤ +0 ∷ (map (_*_ (x +ℤ y)) zs +p ((xs *p (z ∷ zs)) +p (ys *p (z ∷ zs))))
  ≡⟨ cong ( (x +ℤ y) * z +ℤ +0 ∷_) (cong (map (_*_ (x +ℤ y)) zs +p_) (*p-+p-distrib-r xs ys (z ∷ zs))) ⟩
     (x +ℤ y) * z +ℤ +0 ∷ (map (_*_ (x +ℤ y)) zs +p ((xs +p ys) *p (z ∷ zs)))
   ∎

*p-comm : ∀ (xs ys : List ℤ)
  → xs *p ys ≡ ys *p xs 
*p-comm ys [] = *pRightEmpty ys
*p-comm [] xs rewrite *pRightEmpty xs = refl 
*p-comm (x ∷ []) (y ∷ []) rewrite *-comm x y = refl 
*p-comm (x1 ∷ x2 ∷ xs) (y ∷ [])  rewrite *-comm x1 y | +-identityʳℤ (x2 * y) | *-comm x2 y | +pLeftEmpty (xs *p [ y ]) | *p-comm xs [ y ] | *p-map-left-single y xs = refl
*p-comm (x ∷ []) (y1 ∷ y2 ∷ ys)  rewrite *-comm x y1 | +-identityʳℤ (x * y2) | *-comm x y2 | +-identityʳℤ (y2 * x) | sym (*p-map-left-single x ys) | *p-comm ys [ x ] | +pLeftEmpty ([ x ] *p ys) = refl  
*p-comm (x1 ∷ x2 ∷ xs) (y1 ∷ y2 ∷ ys) =
   begin
    (x1 ∷ x2 ∷ xs) *p (y1 ∷ y2 ∷ ys)
  ≡⟨⟩
    (map  (x1 *_) (y1 ∷ y2 ∷ ys)) +p (+0 ∷ (x2 ∷ xs) *p (y1 ∷ y2 ∷ ys))
  ≡⟨ cong (λ z → (map  (x1 *_) (y1 ∷ y2 ∷ ys)) +p (+0 ∷ z)) ( *p-comm (x2 ∷ xs) (y1 ∷ y2 ∷ ys)) ⟩
    (map  (x1 *_) (y1 ∷ y2 ∷ ys)) +p (+0 ∷  ((y1 ∷ y2 ∷ ys) *p (x2 ∷ xs)) )
   ≡⟨⟩
     (map  (x1 *_) (y1 ∷ y2 ∷ ys)) +p (+0 ∷  ((map (y1 *_) (x2 ∷ xs)) +p (+0 ∷ ((y2 ∷ ys) *p (x2 ∷ xs)))))
  ≡⟨ cong (λ z → ((map  (x1 *_) (y1 ∷ y2 ∷ ys)) +p (+0 ∷  ((map (y1 *_) (x2 ∷ xs)) +p (+0 ∷ (z)))))) (*p-comm (y2 ∷ ys) (x2 ∷ xs) ) ⟩
    (map  (x1 *_) (y1 ∷ y2 ∷ ys)) +p (+0 ∷  ((map (y1 *_) (x2 ∷ xs)) +p (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys)))))
  ≡⟨⟩
    ((x1 * y1) ∷ (map  (x1 *_) (y2 ∷ ys))) +p (+0 ∷  ((map (y1 *_) (x2 ∷ xs)) +p (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys)))))
  ≡⟨⟩
    (x1 * y1) +ℤ +0 ∷ (((map  (x1 *_) (y2 ∷ ys))) +p ((map (y1 *_) (x2 ∷ xs)) +p (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys)))))
  ≡⟨ cong (λ z → ((x1 * y1) +ℤ +0 ∷ (z))) (sym (+p-assoc ((map  (x1 *_) (y2 ∷ ys))) (map (y1 *_) (x2 ∷ xs)) (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys))))) ⟩
    (x1 * y1) +ℤ +0 ∷ ((((map  (x1 *_) (y2 ∷ ys))) +p (map (y1 *_) (x2 ∷ xs))) +p (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys))))
  ≡⟨ cong (λ z → ((x1 * y1) +ℤ +0 ∷ ((z) +p (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys)))))) (+p-comm (map  (x1 *_) (y2 ∷ ys)) (map (y1 *_) (x2 ∷ xs)))  ⟩
    (x1 * y1) +ℤ +0 ∷ (((map (y1 *_) (x2 ∷ xs)) +p (map  (x1 *_) (y2 ∷ ys))) +p (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys))))
  ≡⟨ cong ((x1 * y1) +ℤ +0 ∷_) (+p-assoc (map (y1 *_) (x2 ∷ xs)) (map  (x1 *_) (y2 ∷ ys)) (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys))))  ⟩
    (x1 * y1) +ℤ +0 ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((map  (x1 *_) (y2 ∷ ys)) +p (+0 ∷ ((x2 ∷ xs) *p (y2 ∷ ys)))))
  ≡⟨⟩
    (x1 * y1) +ℤ +0 ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((x1 ∷ x2 ∷ xs) *p (y2 ∷ ys)))
  ≡⟨ cong (λ z → (z ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((x1 ∷ x2 ∷ xs) *p (y2 ∷ ys))))) (+-identityʳℤ (x1 * y1))  ⟩
    (x1 * y1)  ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((x1 ∷ x2 ∷ xs) *p (y2 ∷ ys)))
  ≡⟨ cong (_∷ ((map (y1 *_) (x2 ∷ xs)) +p ((x1 ∷ x2 ∷ xs) *p (y2 ∷ ys)))) (*-comm x1 y1) ⟩
    (y1 * x1)  ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((x1 ∷ x2 ∷ xs) *p (y2 ∷ ys)))
  ≡⟨ cong (λ z → ((y1 * x1)  ∷ ((map (y1 *_) (x2 ∷ xs)) +p (z)))) (*p-comm (x1 ∷ x2 ∷ xs)  (y2 ∷ ys)) ⟩
    (y1 * x1)  ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((y2 ∷ ys) *p (x1 ∷ x2 ∷ xs) ))
  ≡⟨ cong (λ z → (z  ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((y2 ∷ ys) *p (x1 ∷ x2 ∷ xs) )))) (sym (+-identityʳℤ (y1 * x1))) ⟩ 
    (y1 * x1) +ℤ +0  ∷ ((map (y1 *_) (x2 ∷ xs)) +p ((y2 ∷ ys) *p (x1 ∷ x2 ∷ xs) ))
  ∎





*p-map-proof : ∀ (x : ℤ) (xs ys : List ℤ)
  → 1 ≤ length ys
  → (x ∷ xs) *p ys ≡ (map (x *_) ys +p (+0 ∷ (xs *p ys)))
*p-map-proof x [] ys z<ys  =  
  begin
    [ x ] *p ys
  ≡⟨ cong ([ x ] *p_) (sym (addZeroes 1 ys z<ys)) ⟩
    ([ x ] *p ([ +0 ] +p ys))
  ≡⟨ sym (*p-+p-distrib-l [ x ] [ +0 ] ys) ⟩
    ([ x ] *p [ +0 ]) +p ([ x ] *p ys)
  ≡⟨⟩
    (((x * +0 +ℤ +0) ∷ [] ) +p ([ x ] *p ys)) 
  ≡⟨ cong (_+p ([ x ] *p ys)) (cong (_∷ []) (+-identityʳℤ (x * +0))) ⟩
    ([ x * +0 ] +p ([ x ] *p ys))
  ≡⟨ cong (_+p ([ x ] *p ys)) (cong (_∷ []) (*-zeroʳℤ x)) ⟩
    ([ +0 ] +p ([ x ] *p ys))
  ≡⟨ +p-comm [ +0 ] ([ x ] *p ys) ⟩
    ([ x ] *p ys) +p [ +0 ]
  ≡⟨ cong (_+p [ +0 ]) (*p-map-left-single x ys) ⟩
    map (_*_ x) ys +p [ +0 ]
   ∎
*p-map-proof x  (z ∷ zs) [ y ]  z<ys = refl   
*p-map-proof x  (z ∷ zs) (y ∷ ys)  z<ys = refl



--properties of length

length-map : ∀ (x : ℤ) (xs : List ℤ)
  → length xs ≡ length (map (x *_) xs)
length-map x [] = refl
length-map x (y ∷ ys) rewrite length-map x ys = refl  


lengthfive : ∀ (y : ℤ) (ys : List ℤ)
  → length ys < length (y ∷ ys)
lengthfive y [] = z<s
lengthfive y1 (y2 ∷ ys) =  s<s ≤-refl

lengthnine : ∀ (y : ℤ)  
  → zero < length ([ y ]) 
lengthnine y =  Data.Nat.z<s


length-single : ∀ (x : ℤ) (ys : List ℤ)
  → length ([ x ] *p ys) ≡ length ys 
length-single x [] = refl
length-single x (y ∷ ys) rewrite length-map x ys | +pRightEmpty (map (x *_) ys) = refl  

length-take : ∀ n (xs : List ℤ) → length (take n xs) ≡ n ⊓ (length xs)
length-take zero  xs  rewrite  takeZero xs = refl 
length-take (suc n) []       = refl
length-take (suc n) (x ∷ xs) = cong ℕ.suc (length-take n xs)

length-drop : ∀ n (xs : List ℤ) → length (drop n xs) ≡ length xs Data.Nat.∸ n
length-drop zero    xs  rewrite dropZero xs = refl  
length-drop (suc n) []       = refl
length-drop (suc n) (x ∷ xs) = length-drop n xs





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
  → shiftRight m (shiftRight n xs) ≡ shiftRight (m + n) xs
shiftRight-shiftRight zero n xs = refl
shiftRight-shiftRight (suc m) n xs rewrite shiftRight-shiftRight m n xs = refl 


shiftRight-+p : ∀ (m : ℕ) (xs ys : List ℤ)
  → shiftRight m (xs +p ys) ≡ shiftRight m xs +p shiftRight m ys
shiftRight-+p zero xs ys = refl
shiftRight-+p (ℕ.suc m) xs ys rewrite shiftRight-+p  m xs ys = refl


shiftRight-len : ∀ (m : ℕ) 
  → length (shiftRight m []) ≡ m
shiftRight-len zero = refl
shiftRight-len (ℕ.suc m) rewrite shiftRight-len m = refl 
  
shiftRight-list-len : ∀ (m : ℕ) (xs : List ℤ)
  → length (shiftRight m xs) ≡ length xs + m 
shiftRight-list-len zero xs  rewrite +-identityʳ (length xs) = refl   
shiftRight-list-len (ℕ.suc m) xs =  
  begin
    suc (length (shiftRight m xs)) --length (shiftRight m xs)
  ≡⟨ cong ℕ.suc (shiftRight-list-len m xs) ⟩
    suc (length xs + m)
  ≡⟨ cong ℕ.suc (+-comm (length xs) m) ⟩
    suc (m + length xs)
  ≡⟨⟩
    suc m + length xs
  ≡⟨ +-comm (suc m) (length xs) ⟩
    length xs + suc m
  ∎

testfo : ∀ (m : ℕ) (a c : List ℤ)
  →  length (a *p c) ≤  length (shiftRight (2 *ℕ m) (a *p c))
testfo m a c rewrite  (shiftRight-list-len (2 *ℕ m) (a *p c)) = m≤m+n (length (a *p c)) (2 *ℕ m)

testthree : ∀ (m : ℕ) (a c : List ℤ) 
  →  (shiftRight (length (a *p c)) []) +p (shiftRight (2 *ℕ m) (a *p c))  ≡ (shiftRight (2 *ℕ m) (a *p c)) 
testthree m a c rewrite  addZeroes (length (a *p c)) (shiftRight (2 *ℕ m) (a *p c)) ( testfo m a c)  = refl



lemmaLen : ∀ (xs ys : List ℤ)
  → length ys ≤ length xs
  → (xs +p ys) -p ys ≡ xs
lemmaLen xs [] xs≥ys rewrite +pRightEmpty xs | +pRightEmpty xs = refl
lemmaLen (x ∷ xs) (y ∷ ys) (s≤s ys≤xs) =
  begin
    ((x +ℤ y ∷ (xs +p ys)) -p (y ∷ ys))
  ≡⟨⟩
    (x +ℤ y) +ℤ ( -i y) ∷ (xs +p ys) -p ys
  ≡⟨ cong (_∷ ((xs +p ys) -p ys)) (+-assocℤ x y (-i y)) ⟩
    (x +ℤ (y +ℤ -i y)) ∷ ((xs +p ys) -p ys)
  ≡⟨ cong (λ z → ((x +ℤ (z)) ∷ ((xs +p ys) -p ys))) (+-inverseʳℤ y) ⟩
    x +ℤ +0 ∷ ((xs +p ys) -p ys)
  ≡⟨ cong (_∷ ((xs +p ys) -p ys)) (+-identityʳℤ x) ⟩
    x  ∷ (xs +p ys) -p ys
  ≡⟨ cong (x ∷_) (+p-assoc xs ys (negPoly ys) ) ⟩
    x ∷ (xs +p (ys -p ys))
  ≡⟨ cong (x ∷_ ) (cong (xs +p_) (negPoly-lemma  ys)) ⟩
    x ∷ (xs +p shiftRight (length ys) [])
  ≡⟨ cong (x ∷_) (+p-comm xs (shiftRight (length ys) [])) ⟩
    x ∷ (shiftRight (length ys) [] +p xs)
  ≡⟨ cong (x ∷_) (addZeroes (length ys) xs ys≤xs)  ⟩
    x ∷ xs
  ∎ 




-----------------------

x+y≡x⊔y : ∀ (xs ys : List ℤ)
  → length (xs +p ys) ≡ length xs ⊔ length ys
x+y≡x⊔y [] ys rewrite +pLeftEmpty ys = refl
x+y≡x⊔y xs [] rewrite +pRightEmpty xs | Data.Nat.Properties.⊔-identityʳ (length xs) = refl  
x+y≡x⊔y (x ∷ xs) (y ∷ ys) rewrite x+y≡x⊔y xs ys = refl  

length-*p : ∀ (xs ys : List ℤ) 
  → zero < length xs
  → zero < length ys
  → length ys ≤ length (xs *p ys)
length-*p (x ∷ xs) ys z<xs z<ys  rewrite *p-map-proof x xs ys z<ys | x+y≡x⊔y (map (x *_) ys) ( +0 ∷ (xs *p ys)) | sym (length-map x ys) = m≤n⇒m≤n⊔o (suc (length (xs *p ys))) (≤-reflexive refl)

zero<lensR : ∀ (m : ℕ) (xs : List ℤ)
  → zero < length xs
  → zero < length (shiftRight m xs)
zero<lensR m xs z<xs rewrite shiftRight-list-len m xs = ≤-stepsʳ m z<xs    

length-lemma : ∀ (m : ℕ) (y : ℤ) (xs ys : List ℤ)
  → zero < length xs
  →   length ys  < length ((shiftRight m xs) *p (y ∷ ys)) 
length-lemma  m y xs ys z<xs  =  length-*p (shiftRight m xs) (y ∷ ys)  (zero<lensR m xs z<xs) z<s 

shiftRight-*p : ∀ (m : ℕ) (xs ys : List ℤ)
  → zero < length xs
  → zero < length ys
  →  shiftRight m (xs *p ys) ≡ (shiftRight m xs) *p ys
shiftRight-*p zero xs ys zero<lenXS zero<lenYS = refl
shiftRight-*p (ℕ.suc m) (x ∷ xs) (y ∷ ys) z<xs z<ys =
           begin
              +0 ∷ shiftRight m ((x ∷ xs) *p (y ∷ ys))
            ≡⟨ cong (+0 ∷_) (shiftRight-*p m (x ∷ xs) (y ∷ ys) z<xs z<ys) ⟩
              +0 ∷ ((shiftRight m (x ∷ xs)) *p (y ∷ ys) ) 
            ≡⟨ cong (+0 ∷_) (equality) ⟩ 
               (+0 ∷ (shiftRight m (x ∷ xs))) *p (y ∷ ys) 
             ∎
             where
              equality : (shiftRight m (x ∷ xs) *p (y ∷ ys)) ≡  (map (_*_ +0) ys +p (shiftRight m (x ∷ xs) *p (y ∷ ys)))
              equality = begin
                       (shiftRight m (x ∷ xs) *p (y ∷ ys))
                     ≡⟨ sym (addZeroes (length ys) (shiftRight m (x ∷ xs) *p (y ∷ ys)) (<⇒≤ (length-lemma  m y (x ∷ xs) ys z<xs ))) ⟩
                       shiftRight (length ys) [] +p (shiftRight m (x ∷ xs) *p (y ∷ ys))
                     ≡⟨ cong (_+p (shiftRight m (x ∷ xs) *p (y ∷ ys))) (sym (map-shiftRight-zero ys)) ⟩
                         (map (_*_ +0) ys +p (shiftRight m (x ∷ xs) *p (y ∷ ys)))
                     ∎



  
shiftRight-two-m : ∀ (m : ℕ) (xs ys : List ℤ)      
  → zero < length xs
  → zero < length ys
  → shiftRight m xs *p shiftRight m ys ≡ shiftRight (2 *ℕ m) (xs *p ys)
shiftRight-two-m zero xs ys z<xs z<ys = refl
shiftRight-two-m (suc m) xs ys z<xs z<ys =
    begin
      (shiftRight (suc m) xs) *p (shiftRight (suc m) ys)
    ≡⟨ sym (shiftRight-*p (suc m) xs (shiftRight (suc m) ys) z<xs z<s) ⟩
        shiftRight (suc m) (xs *p shiftRight (suc m) ys)
    ≡⟨ cong₂ shiftRight (refl) (*p-comm xs (shiftRight (suc m) ys)) ⟩
        shiftRight (suc m) ((shiftRight (suc m) ys) *p xs)
    ≡⟨ cong₂ shiftRight (refl)(sym (shiftRight-*p (suc m) ys xs z<ys z<xs)) ⟩ 
        shiftRight (suc m) ((shiftRight (suc m) (ys *p xs)))
    ≡⟨ shiftRight-shiftRight (suc m) (suc m) (ys *p xs) ⟩
        +0 ∷ shiftRight (m + suc m) (ys *p xs) 
    ≡⟨ cong (+0 ∷_) (cong₂ shiftRight (cong (m +_) (cong suc (sym (+-identityʳ m)))) (*p-comm ys xs)) ⟩
        +0 ∷ shiftRight (m + suc (m + zero )) (xs *p ys)
      ∎





n>2⇒0<n : ∀ (n : ℕ)
  → 2 < n
  → 0 < n
n>2⇒0<n  n two<n = ≤-trans  z<s two<n

length-lemma-two : ∀  (y : ℤ) (xs ys : List ℤ)
  → zero < length xs
  →   length ys  < length (xs *p (y ∷ ys)) 
length-lemma-two  y xs ys z<xs  =  length-*p (xs) (y ∷ ys) z<xs  z<s



test : ∀ {m n o : ℕ} → m ≤ o → n ≤ o → (m ⊓ n) ⊓  o ≡ m ⊓ n 
test  {zero} _ _    =  refl 
test {suc m} {zero} _ z≤o = refl  
test  {suc m} {suc n} {suc o} (s≤s m≤o) (s≤s n≤o) = cong suc (test  m≤o n≤o)


lengthTakeMin : ∀ (m n : ℕ) (xs : List ℤ)
    → m ⊓ n ≤ length xs
    → length (take (m ⊓ n) xs) ≡ m ⊓ n 
lengthTakeMin m n xs  m⊓n≤xs  rewrite length-take (m ⊓ n) xs | m≤n⇒m⊓n≡m m⊓n≤xs = refl 

lengthDropMin : ∀ (m n : ℕ) (xs : List ℤ)
    → m ⊓ n ≤ length xs
    → length (drop (m ⊓ n) xs) ≡ (length xs) ∸ m ⊓ n 
lengthDropMin m n xs  m⊓n≤xs rewrite length-drop (m ⊓ n) xs = refl    
