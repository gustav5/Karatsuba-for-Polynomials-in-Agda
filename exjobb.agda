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
open import Data.Empty using (⊥; ⊥-elim)
open import libExjobb 








--------------------------
--------------------------x
-- Karatsuba


karatsuba' : ℕ → List ℤ → List ℤ → List ℤ
karatsuba' zero xs ys = xs *p ys
karatsuba' (suc n) xs ys = if ((((length xs) / 2) ⊓ (length ys / 2)) ≤ᵇ' 2)
                           then (xs *p ys)
                           else
                           let m = ((length xs / 2) ⊓ (length ys / 2)) in
                           let (b , a) = splitAt m xs in
                           let (d , c) = splitAt m ys in
                           let ac = karatsuba' n a c in 
                           let bd = karatsuba' n b d in
                           let ad_plus_bc = ((karatsuba' n (a +p b) (c +p d) -p ac) -p bd) in
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd


karatsuba : List ℤ → List ℤ → List ℤ
karatsuba [] ys = []
karatsuba xs [] = []
karatsuba xs ys = karatsuba' ((length xs) Data.Nat.⊔ (length ys)) xs ys




--------------------------
---------------   in progress
   


xs-take-drop : ∀  (n : ℕ) (xs : List ℤ)
  → (take n xs) +p (shiftRight n (drop n xs)) ≡ xs
xs-take-drop zero xs rewrite takeZero xs | dropZero xs | +pLeftEmpty xs = refl
xs-take-drop (ℕ.suc n) (x ∷ xs) rewrite +-identityʳ x | xs-take-drop n xs = refl 
xs-take-drop n xs = {!!}


-------------------------------------------
---------------- properties


--properties of length

lemmaLen : ∀ (xs ys : List ℤ)
  → length ys ≤ℕ length xs
  → (xs +p ys) -p ys ≡ xs
lemmaLen xs [] xs≥ys rewrite +pRightEmpty xs | +pRightEmpty xs = refl
lemmaLen (x ∷ xs) (y ∷ ys) (s≤s ys≤xs) =
  begin
    ((x + y ∷ (xs +p ys)) -p (y ∷ ys))
  ≡⟨⟩
    (x + y) + ( - y) ∷ (xs +p ys) -p ys
  ≡⟨ cong (_∷ ((xs +p ys) -p ys)) (+-assoc x y (- y)) ⟩
    (x + (y + - y)) ∷ ((xs +p ys) -p ys) 
  ≡⟨ cong (_∷ ((xs +p ys) -p ys)) (cong₂ (_+_) (refl) ((+-inverseʳ y))  ) ⟩ -- hjälp max, varför gult
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


-- hole in proof
length-lemma : ∀ (m : ℕ) (y : ℤ) (xs ys : List ℤ)
  → zero <ℕ length xs
  → length ys ≤ℕ length (shiftRight m (xs) *p (y ∷ ys))
length-lemma  zero y xs ys  z<xs  = {!  !}
length-lemma (suc n) y xs ys z<xs   rewrite map-shiftRight-zero ys = {!!} -- {!!} -- rewrite addZeroes ys ys<yys 

shiftRight-*p : ∀ (m : ℕ) (xs ys : List ℤ)
  → zero <ℕ length xs
  → zero <ℕ length ys
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
                     ≡⟨ sym (addZeroes (length ys) (shiftRight m (x ∷ xs) *p (y ∷ ys)) (length-lemma m y (x ∷ xs) ys zero<lenXS)) ⟩
                       shiftRight (length ys) [] +p (shiftRight m (x ∷ xs) *p (y ∷ ys))
                     ≡⟨ cong (_+p (shiftRight m (x ∷ xs) *p (y ∷ ys))) (sym (map-shiftRight-zero ys)) ⟩
                         (map (_*_ +0) ys +p (shiftRight m (x ∷ xs) *p (y ∷ ys)))
                     ∎





zeroleq : ∀ (m : ℕ) 
  → (m) ≤ℕ zero
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






map-lemma : ∀ (xs ys : List ℤ)
  → (+0 ∷ xs) *p ys ≡ map (+0 *_) ys +p (+0 ∷ (xs *p ys))
map-lemma [] ys = {!!}
map-lemma (x ∷ xs) ys = {!!}



-- distributivity *p over +p    


    --x  ∷ (xs +p ys) +p negPoly ys
  --≡⟨⟩
    --{!!}
-- ≡⟨ cong (x ∷_) ( lemmaLen xs ys ys≤xs) ⟩
  --  x ∷ xs
 -- ∎

len :  ∀ (ys : List ℤ)
  → 0 <ℕ length ys 
  → (1 ≤ᵇ' length ys) ≡ true
len ys 0<ys = {!!}  
  --begin
  --  1 ≤ᵇ' (ℕ.suc (length ys))
 -- ≡⟨⟩
    --{!!}

*p-map-proof : ∀ (x : ℤ) (xs ys : List ℤ)
  → (x ∷ xs) *p ys ≡ (map (x *_) ys +p (+0 ∷ (xs *p ys)))
*p-map-proof x [] ys   =  --rewrite *p-map-left-single x ys | addZeroes 1 []  
  begin
    [ x ] *p ys
  ≡⟨ cong ([ x ] *p_) (sym (addZeroes 1 ys {!!})) ⟩
    ([ x ] *p ([ +0 ] +p ys))
  ≡⟨ sym (*p-+p-distrib-l [ x ] [ +0 ] ys) ⟩
    ([ x ] *p [ +0 ]) +p ([ x ] *p ys)
  ≡⟨⟩
    (((x * +0 + +0) ∷ [] ) +p ([ x ] *p ys)) 
  ≡⟨ cong (_+p ([ x ] *p ys)) (cong (_∷ []) (+-identityʳ (x * +0))) ⟩
    ([ x * +0 ] +p ([ x ] *p ys))
  ≡⟨ cong (_+p ([ x ] *p ys)) (cong (_∷ []) (*-zeroʳ x)) ⟩
    ([ +0 ] +p ([ x ] *p ys))
  ≡⟨ +p-comm [ +0 ] ([ x ] *p ys) ⟩
    ([ x ] *p ys) +p [ +0 ]
  ≡⟨ cong (_+p [ +0 ]) (*p-map-left-single x ys) ⟩
    map (_*_ x) ys +p [ +0 ]
   ∎
*p-map-proof x  (z ∷ zs) ys  =
  begin
    ((x ∷ z ∷ zs) *p ys)
  ≡⟨⟩
    ((x ∷ z ∷ zs) *p ys)
  ≡⟨ {!!} ⟩
    (map (x *_) ys +p (+0 ∷ (map (z *_) ys))) +p (+0 ∷ (zs *p ys))
  ≡⟨ {!!} ⟩
    map (x *_) ys +p (+0 ∷ (map (z *_) ys +p (+0 ∷ (zs *p ys))))
  ≡⟨ cong (map (x *_) ys +p_) ( cong (+0 ∷_) (sym (*p-map-proof z zs ys))) ⟩
    map (x *_) ys +p (+0 ∷ ((z ∷ zs) *p ys))
  ∎
  
*p-comm : ∀ (xs ys : List ℤ)
  → xs *p ys ≡ ys *p xs
*p-comm [] ys  rewrite *pRightEmpty ys = refl
*p-comm xs []  rewrite *pRightEmpty xs = refl
*p-comm (x ∷ xs) (y ∷ ys)  =
  begin
    x * y + +0 ∷ (map (_*_ x) ys +p (xs *p (y ∷ ys)))
  ≡⟨ cong (_∷ (map (_*_ x) ys +p (xs *p (y ∷ ys)))) (+-identityʳ  (x * y)) ⟩
    x * y ∷ (map (_*_ x) ys +p (xs *p (y ∷ ys)))
 ≡⟨ cong (x * y ∷_) (cong ((map (_*_ x) ys) +p_)  (*p-comm xs (y ∷ ys))) ⟩
   x * y ∷ (map (_*_ x) ys +p ((y ∷ ys) *p xs))
  ≡⟨ cong (x * y ∷_) (cong ((map (_*_ x) ys) +p_)  (*p-map-proof y ys xs )) ⟩
    x * y ∷ (map (_*_ x) ys +p (map (y *_) xs +p (+0 ∷ (ys *p xs))))
  ≡⟨ cong (x * y ∷_) (sym (+p-assoc (map (_*_ x) ys) (map (y *_) xs) (+0 ∷ (ys *p xs)))) ⟩
     x * y ∷ ((map (_*_ x) ys +p map (y *_) xs) +p (+0 ∷ (ys *p xs)))
  ≡⟨ cong (x * y ∷_) (cong (_+p (+0 ∷ (ys *p xs))) (+p-comm (map (_*_ x) ys) (map (y *_) xs))) ⟩
     x * y ∷ ((map (y *_) xs +p map (_*_ x) ys) +p (+0 ∷ (ys *p xs)))
  ≡⟨ cong (x * y ∷_) (+p-assoc (map (y *_) xs) (map (_*_ x) ys) (+0 ∷ (ys *p xs))) ⟩
    x * y ∷ (map (y *_) xs +p (map (_*_ x) ys +p (+0 ∷ (ys *p xs))))
  ≡⟨ cong (x * y ∷_) (cong (map (y *_) xs +p_) (cong (map (x *_) ys +p_) (cong (+0 ∷_)  (*p-comm ys xs)))) ⟩
    x * y ∷  (map (y *_) xs +p (map (x *_) ys +p (+0 ∷ (xs *p ys))))
  ≡⟨ cong (x * y ∷_) (cong (map (y *_) xs +p_) (sym (*p-map-proof x xs ys)))  ⟩
    x * y ∷ (map (y *_) xs +p ((x ∷ xs) *p ys))
  ≡⟨ cong (_∷ (map (y *_) xs +p ((x ∷ xs) *p ys))) (*-comm x y) ⟩
    y * x ∷ (map (y *_) xs +p ((x ∷ xs) *p ys))
  ≡⟨ cong (_∷ (map (y *_) xs +p ((x ∷ xs) *p ys))) (sym (+-identityʳ  (y * x))) ⟩
    y * x + +0 ∷ (map (y *_) xs +p ((x ∷ xs) *p ys))
  ≡⟨ cong ((y * x + +0) ∷_) (cong (map (y *_) xs +p_) (*p-comm (x ∷ xs) ys)) ⟩
    y * x + +0 ∷ (map (y *_) xs +p (ys *p (x ∷ xs))) 
  ∎

  
-------------------


shiftRight-two-m : ∀ (m : ℕ) (xs ys : List ℤ)
  → zero <ℕ length xs
  → zero <ℕ length (shiftRight m ys)
  → shiftRight m xs *p shiftRight m ys ≡ shiftRight (2 Data.Nat.* m) (xs *p ys)
shiftRight-two-m zero xs ys z<xs z<ys = refl
shiftRight-two-m (ℕ.suc m) xs ys z<xs z<srys =
  begin
    (shiftRight (ℕ.suc m) xs) *p (shiftRight (ℕ.suc m) ys)
  ≡⟨ sym (shiftRight-*p (ℕ.suc m) xs (shiftRight (ℕ.suc m) ys) z<xs z<srys) ⟩
    shiftRight (ℕ.suc m) (xs *p shiftRight (ℕ.suc m) ys)
  ≡⟨ {!!} ⟩ --cong
    shiftRight (ℕ.suc m) ((shiftRight (ℕ.suc m) ys) *p xs)
  ≡⟨ {!!} ⟩ --cong inside shiftRight
    shiftRight (ℕ.suc m) ((shiftRight (ℕ.suc m) (ys *p xs)))
  ≡⟨ shiftRight-shiftRight (ℕ.suc m) (ℕ.suc m) (ys *p xs) ⟩
    +0 ∷ shiftRight (m +ℕ ℕ.suc m) (ys *p xs) 
  ≡⟨ {!!} ⟩
    +0 ∷ shiftRight (m +ℕ ℕ.suc (m +ℕ zero )) (xs *p ys)
  ∎


--shiftRight (ℕ.suc m) (shiftRight (ℕ.suc m) (xs *p ys))
  --≡⟨ {!!} ⟩
   -- {!!}




lemmaThree : ∀ (xs ys zs rs : List ℤ)
  → ((xs +p ys) *p (zs +p rs)) +p (negPoly (xs *p zs)) ≡ (xs *p rs) +p ((ys *p zs) +p (ys *p rs))
lemmaThree [] ys zs rs rewrite +pLeftEmpty ys | +pRightEmpty (ys *p (zs +p rs)) | sym (*p-+p-distrib-l ys zs rs) | +pLeftEmpty ((ys *p zs) +p (ys *p rs)) = refl
lemmaThree xs [] zs rs rewrite +pRightEmpty xs |  sym (*p-+p-distrib-l xs zs rs) | +p-comm (xs *p zs) (xs *p rs) | +p-assoc (xs *p rs) (xs *p zs) (negPoly (xs *p zs)) | negPoly-lemma (xs *p zs) = {!!}
lemmaThree xs ys [] rs rewrite +pLeftEmpty rs | *pRightEmpty xs  | sym(*p-+p-distrib-r xs ys rs) | +p-assoc (xs *p rs) (ys *p rs) [] | +p-comm (ys *p rs) [] | *pRightEmpty ys = refl     --= {!!} --+pRightEmpty ((xs +p ys) *p rs) = {!!} 
lemmaThree xs ys zs [] = {!!} 
lemmaThree (x ∷ xs) (y ∷ ys) (z ∷ zs) (r ∷ rs) = -- {!!}  -- rewrite +-identityʳ (x * z) = {!!}  
  begin
    (x + y) * (z + r) + +0 + - (x * z + +0) ∷ ((map (_*_ (x + y)) (zs +p rs) +p ((xs +p ys) *p (z + r ∷ (zs +p rs)))) +p negPoly (map (_*_ x) zs +p (xs *p (z ∷ zs))))
  ≡⟨ cong ((x + y) * (z + r) + +0 + - (x * z + +0) ∷_)   (cong (_+p (negPoly (map (_*_ x) zs +p (xs *p (z ∷ zs))))) (cong (_+p ((xs +p ys) *p (z + r ∷ (zs +p rs)))) (sym (map-+p-dist-two x y (zs +p rs)))))                ⟩
    (x + y) * (z + r) + +0 + - (x * z + +0) ∷ (((map (_*_ x) (zs +p rs) +p map (_*_ y) (zs +p rs)) +p ((xs +p ys) *p (z + r ∷ (zs +p rs)))) +p negPoly (map (_*_ x) zs +p (xs *p (z ∷ zs))))
  ≡⟨ cong ((x + y) * (z + r) + +0 + - (x * z + +0) ∷_)   (cong (_+p (negPoly (map (_*_ x) zs +p (xs *p (z ∷ zs))))) (cong (_+p ((xs +p ys) *p (z + r ∷ (zs +p rs)))) (cong₂ (_+p_) (sym (map-+p-distrib x zs rs)) (sym (map-+p-distrib y zs rs)))))  ⟩
    (x + y) * (z + r) + +0 + - (x * z + +0) ∷ ((((map (_*_ x) zs +p map (_*_ x) rs) +p (map (_*_ y) zs +p map (_*_ y) rs)) +p ((xs +p ys) *p (z + r ∷ (zs +p rs)))) +p negPoly (map (_*_ x) zs +p (xs *p (z ∷ zs))))
  ≡⟨⟩
    {!!}



lengthsix : ∀ (x : ℤ) (xs ys : List ℤ)
  → 1 ≤ℕ length xs
  → 1 ≤ℕ length ys
  → (length (x ∷ xs *p ys)) ≡ length xs +ℕ length ys 
lengthsix x xs ys z<xs z<ys =
  begin
    ℕ.suc (length (xs *p ys))
  ≡⟨⟩
    (length (x ∷ xs *p ys))
  ≡⟨ {!!} ⟩
    (length ((map (x *_) ys) +p ( +0 ∷  xs *p ys)))
  ≡⟨ lengthseven (map (x *_) ys) ( +0 ∷  xs *p ys) ⟩
    length (map (x *_) ys) ⊔ ℕ.suc (length (xs *p ys))
  ≡⟨ {!!} ⟩
    ℕ.suc (length (xs *p ys))
  ≡⟨⟩
    {!!}
{-

ℕ.suc (length ((map (x *_) ys) +p ( +0 ∷  xs *p ys)))
  ≡⟨ cong ℕ.suc (lengthseven (map (x *_) ys) ( +0 ∷  xs *p ys)) ⟩
    ℕ.suc (length (map (x *_) ys) ⊔ ℕ.suc (length (xs *p ys)))
  ≡⟨ {!!} ⟩
    ℕ.suc (ℕ.suc (length (xs *p ys)))
  ≡⟨ cong ℕ.suc (lengthsix xs ys {!!}  z<ys ) ⟩
    {!!}-}

length-three : ∀ (as bs xs : List ℤ)
  → zero <ℕ length as → zero <ℕ length bs → zero <ℕ length xs
  → length (as *p bs) ≤ℕ length (xs *p (as *p bs))
length-three as bs xs z<as z<bs z<xs = {!!}  

lengthfour : ∀ (a c x : List ℤ)
  → zero <ℕ length a → zero <ℕ length b  → zero <ℕ length c 
  → length(a *p c) ≤ℕ length ((x *p a) +p (x *p c))
lengthfour a c x z<a z<c z<x rewrite *p-+p-distrib-l x a c  = {!!} -- | length-three (a *p c) x  z<a z<c z<x = ?  

lemmaFive : ∀ (a b c d : List ℤ)
  → zero <ℕ length a → zero <ℕ length b  → zero <ℕ length c → zero <ℕ length d 
  → length (a *p c)  ≤ℕ length ((a *p d) +p ((b *p d) +p (b *p c)))
lemmaFive a b c d z<a z<b z<c z<d = {!!} --if length a *p cm


lengths-add : ∀ (xs ys : List ℤ)
  → zero <ℕ length xs
  → zero <ℕ length ys
  → length xs +ℕ length ys ≡ length (xs *p ys)
lengths-add (x ∷ []) (y ∷ ys) z<xs z<ys = {!!} 
lengths-add (x ∷ xs) ys z<xs z<ys = {!!} 



--lemmaFive [] b c d rewrite +pRightEmpty (b *p c) | +p-assoc [] (b *p d) (b *p c) = refl
--lemmaFive a [] c d = {!!}
--lemmaFive a b [] d = {!!} 


lemmaFour : ∀ (a b c d : List ℤ)
  → zero <ℕ length a → zero <ℕ length b  → zero <ℕ length c → zero <ℕ length d 
  → ((a +p b) *p (c +p d)) +p (negPoly (a *p c)) ≡ (a *p d) +p ((b *p c) +p (b *p d))
lemmaFour a b c d z<a z<b z<c z<d rewrite sym (*p-+p-distrib-l (a +p b) c d) | sym (*p-+p-distrib-r a b c) | sym (*p-+p-distrib-r a b d) | +p-comm ((a *p c) +p (b *p c)) ((a *p d) +p (b *p d)) | +p-assoc ((a *p d) +p (b *p d))  ((a *p c) +p (b *p c))  (negPoly (a *p c)) | +p-comm (a *p c) (b *p c) | +p-assoc (b *p c) (a *p c) (negPoly (a *p c)) | negPoly-lemma (a *p c) | +p-rearrange (a *p d) (b *p d) (b *p c) ( shiftRight (length (a *p c)) []) | +p-comm  ((a *p d) +p ((b *p d) +p (b *p c)))  (shiftRight (length (a *p c)) []) | addZeroes (length (a *p c))  ((a *p d) +p ((b *p d) +p (b *p c))) (lemmaFive a b c d  z<a z<b z<c z<d) | +p-comm (b *p d) (b *p c) = refl

ad+bc : ∀ (xs ys zs rs : List ℤ)
  → zero <ℕ length xs →  zero <ℕ length ys → zero <ℕ length zs → zero <ℕ length rs 
  → (((xs +p ys) *p (zs +p rs)) -p (xs *p zs)) -p (ys *p rs) ≡ (xs *p rs) +p (ys *p zs)
ad+bc xs ys zs rs z<xs z<ys z<zs z<rs rewrite lemmaFour xs ys zs rs z<xs z<ys z<zs z<rs = {!!}  -- | *p-+p-distrib-l ys zs rs = {!!} 
{-
  begin
    (((xs +p ys) *p (zs +p rs)) -p (xs *p zs)) -p (ys *p rs)
  ≡⟨⟩
    (((xs +p ys) *p (zs +p rs)) +p negPoly (xs *p zs) ) -p (ys *p rs)
  ≡⟨ cong (_-p (ys *p rs)) (lemmaFour xs ys zs rs z<xs z<ys z<zs z<rs) ⟩
    ((xs *p rs) +p ((ys *p zs) +p (ys *p rs))) +p negPoly (ys *p rs)
  ≡⟨ cong (_+p negPoly (ys *p rs)) () ⟩
  --≡⟨ +p-assoc (xs *p rs)  ((ys *p zs) +p (ys *p rs)) (negPoly (ys *p rs)) ⟩
   --  ((xs *p rs) +p (((ys *p zs) +p (ys *p rs)) +p negPoly (ys *p rs)))
  --≡⟨⟩
    {!!}-}

ad+bc-two : ∀ (xs ys zs rs : List ℤ)
  → (((xs +p ys) *p (zs +p rs)) -p (xs *p zs)) -p (ys *p rs) ≡ (xs *p rs) +p (ys *p zs)
ad+bc-two xs ys zs rs = 
  begin
    (((xs +p ys) *p (zs +p rs)) -p (xs *p zs)) -p (ys *p rs)
  ≡⟨ cong (_-p (ys *p rs)) (cong (_-p  (xs *p zs)) (sym (*p-+p-distrib-l (xs +p ys) zs rs))) ⟩
    ((((xs +p ys) *p zs) +p ((xs +p ys) *p rs)) -p (xs *p zs)) -p (ys *p rs)    
  ≡⟨ cong (_-p (ys *p rs)) (cong (_-p  (xs *p zs)) (cong₂ (_+p_) (sym (*p-+p-distrib-r xs ys zs)) (sym (*p-+p-distrib-r xs ys rs)))) ⟩
    ((((xs *p zs) +p (ys *p zs)) +p ((xs *p rs) +p (ys *p rs))) +p negPoly (xs *p zs)) +p negPoly (ys *p rs)
  ≡⟨ cong (_+p negPoly (ys *p rs)) (cong (_+p negPoly (xs *p zs)) (cong (_+p ((xs *p rs) +p (ys *p rs))) (+p-comm (xs *p zs) (ys *p zs))))  ⟩ 
    (((((ys *p zs) +p (xs *p zs)) +p ((xs *p rs) +p (ys *p rs))) +p negPoly (xs *p zs)) +p negPoly (ys *p rs))
  ≡⟨ cong (_+p negPoly (ys *p rs)) (cong (_+p negPoly (xs *p zs)) ( +p-assoc-two (ys *p zs) (xs *p zs) (xs *p rs) (ys *p rs))) ⟩
    (((((ys *p zs) +p (xs *p rs)) +p ((xs *p zs) +p (ys *p rs))) +p negPoly (xs *p zs)) +p negPoly (ys *p rs))
  ≡⟨ cong (_+p negPoly (ys *p rs)) (+p-assoc ((ys *p zs) +p (xs *p rs))  ((xs *p zs) +p (ys *p rs)) (negPoly (xs *p zs))) ⟩
    ((((ys *p zs) +p (xs *p rs)) +p (((xs *p zs) +p (ys *p rs)) +p negPoly (xs *p zs))) +p negPoly (ys *p rs))
   ≡⟨ cong (_+p negPoly (ys *p rs)) (cong (((ys *p zs) +p (xs *p rs)) +p_) (cong  (_+p  negPoly (xs *p zs)) (+p-comm (xs *p zs) (ys *p rs))))  ⟩
    ((((ys *p zs) +p (xs *p rs)) +p (((ys *p rs) +p (xs *p zs)) +p negPoly (xs *p zs))) +p negPoly (ys *p rs))
   ≡⟨ cong (_+p negPoly (ys *p rs)) (cong (((ys *p zs) +p (xs *p rs)) +p_) (+p-assoc (ys *p rs) (xs *p zs) (negPoly (xs *p zs))))  ⟩
     ((((ys *p zs) +p (xs *p rs)) +p ((ys *p rs) +p ((xs *p zs) +p negPoly (xs *p zs)))) +p negPoly (ys *p rs))
   ≡⟨ cong (_+p negPoly (ys *p rs)) (cong (((ys *p zs)  +p (xs *p rs)) +p_) (cong ((ys *p rs) +p_) (negPoly-lemma  (xs *p zs)) )) ⟩
     {!!}




  --≡⟨ cong ((xs *p rs) +p_) (cong (_+p negPoly (ys *p rs)) ( cong ((ys *p zs) +p_) (*p-comm ys rs))) ⟩
   --  ((xs *p rs) +p (((ys *p zs) +p (rs *p ys)) +p negPoly (ys *p rs)))
  -- ≡⟨ cong ((xs *p rs) +p_)  (lemmaFour ys zs rs ys z<ys z<zs z<rs z<ys) ⟩
   --  ?
     
--| negPoly-lemma (ys *p rs) | +p-comm (ys *p zs) (shiftRight (length (ys *p rs)) []) = {!!}  -- | addZeroes (shiftRight (length (ys *p rs)) [] +p (ys *p zs)) = ?  --| if (length (ys *p rs)) ≤ᵇ' (length (ys *p zs)) then ? else ?

min-length : ∀ (xs ys : List ℤ) 
  → length xs / 2 ⊓ (length ys / 2) ≤ℕ length xs
min-length [] ys = z≤n
--min-length xs [] =   (length xs) ⊓-zeroʳ  0 --= ?  -- rewrite ⊓-zeroʳ = ? --    = {!!}  -- = ?  length xs / 2 ⊓ (length ys / 2
min-length (x ∷ xs) ys = {!!}

min-length-two : ∀ (xs ys : List ℤ) 
  → length xs / 2 ⊓ (length ys / 2) ≤ℕ length ys
min-length-two xs [] = {!!} 
--min-length xs [] =   (length xs) ⊓-zeroʳ  0 --= ?  -- rewrite ⊓-zeroʳ = ? --    = {!!}  -- = ?  length xs / 2 ⊓ (length ys / 2
min-length-two xs (y ∷ ys) = {!!}



--min-len : ∀ (x y : ℕ)
--  → x / 2 ⊓ y / 2 ≤ℕ



half : ∀ (n : ℕ)
  → n / 2 ≤ℕ n
half n =  m/n≤m n 2 



returnmin : List ℤ → List ℤ → List ℤ
returnmin xs ys = if (length xs) ≤ᵇ' (length ys)
                                        then xs
                                        else ys
                                        

returnmax : List ℤ → List ℤ → List ℤ
returnmax xs ys = if (length xs) ≤ᵇ' (length ys)
                                        then ys
                                        else xs
                     


minLen : ∀ (x y : ℕ)
  → x / 2 ⊓ y / 2  ≤ℕ x 
minLen x y  = {!!} --rewrite  with x  y |                     ?    {!!} --(Data.Nat.Properties.m≤n⇒m⊓n≡m  x y x≤y)  ≤ℕ x  -- 
                                                                       -- x ≤ᵇ' y
                                                                       -- | true = m/n≤m x 2
                                                                       -- | false = ≤-trans (m/n≤m y 2)


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
                           let ad_plus_bc = ((karatsuba' n (a +p b) (c +p d) -p ac) -p bd) in
                           xs *p ys
                         ≡⟨ cong₂ (_*p_) (split-p-new  m xs (min-length  xs ys)) (split-p-new  m ys (min-length-two xs ys)) ⟩  --length conditional missing in karatsuba. done with split-p
                           (b +p shiftRight m a) *p (d +p shiftRight m c)
                         ≡⟨ sym (*p-+p-distrib-r b (shiftRight m a) (d +p shiftRight m c)) ⟩
                           (b *p (d +p shiftRight m c)) +p ((shiftRight m a) *p (d +p shiftRight m c))
                         ≡⟨ cong₂ (_+p_) (sym (*p-+p-distrib-l b d (shiftRight m c))) (sym (*p-+p-distrib-l (shiftRight m a) d (shiftRight m c))) ⟩
                           ((b *p d) +p (b *p (shiftRight m c))) +p (((shiftRight m a) *p d) +p (shiftRight m a *p shiftRight m c))
                         ≡⟨ +p-rearrange (b *p d) (b *p (shiftRight m c)) ((shiftRight m a) *p d)  (shiftRight m a *p shiftRight m c) ⟩          
                           ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p (shiftRight m a *p shiftRight m c)
                         ≡⟨ cong (((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p_) ({!!} ) ⟩
                           ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p ((shiftRight (2 *ℕ m) (a *p c)))          -- shiftRight-+p done. shiftRight-*p not done, need conditional for length . *p-comm would be nic
                         ≡⟨ {!!} ⟩                                                                                                                                                                                                           -- ad+bc, just started
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd ∎
                           

