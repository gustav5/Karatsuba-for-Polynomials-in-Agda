import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Nat renaming( _*_ to _*ℕ_)   --using (ℕ; zero; suc; _⊓_; _⊔_ ;z≤n; s≤s;z<s;s<s) renaming( _*_ to _*ℕ_ ;_+_ to _+ℕ_;_<?_ to _<?ℕ_; _≤?_ to  _≤?ℕ_; _≤_ to _≤ℕ_; _<_ to _<ℕ_;_≥_ to  _≥ℕ_ ) hiding (-)
open import Data.Nat.Properties renaming(*-comm to *-commℕ)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer  using (ℤ;+0;_*_) renaming (_+_ to _+ℤ_; -_ to -i_) 
open import Data.Integer.Properties hiding(_≤?_;≰⇒>;_<?_;m≤n⇒m⊔n≡n;≤-reflexive;<⇒≤;m≤n⇒m⊓n≡m) renaming (*-zeroʳ to *-zeroʳℤ;*-zeroˡ to *-zeroˡℤ;+-inverseʳ to +-inverseʳℤ; +-identityʳ to +-identityʳℤ;+-identityˡ to +-identityˡℤ;+-comm to +-commℤ;*-distribʳ-+ to *-distribʳ-+ℤ;*-distribˡ-+ to *-distribˡ-+ℤ;≤-refl to ≤-reflℤ;+-assoc to +-assocℤ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Level using (Level)
open import Data.Nat.DivMod
--open import Data.Integer.Base hiding (_⊓_;_/_;_⊔_) 
open import Data.Empty using (⊥; ⊥-elim)
open import libExjobb 



--------------------------
--------------------------
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

karatsuba'' : ℕ → List ℤ → List ℤ → List ℤ
karatsuba'' zero xs ys = xs *p ys
karatsuba'' (suc n) xs ys with ((((length xs) / 2) ⊓ (length ys / 2)) ≤? 2)
...   | (yes _) = (xs *p ys)
...   | (no _) =
                           let m = ((length xs / 2) ⊓ (length ys / 2)) in
                           let b = take m xs in
                           let a = drop m xs in
                           let d  = take m ys in
                           let c = drop m ys in
                           let ac = karatsuba'' n a c in 
                           let bd = karatsuba'' n b d in
                           let ad_plus_bc = ((karatsuba'' n (a +p b) (c +p d) -p ac) -p bd) in
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd


karatsuba : List ℤ → List ℤ → List ℤ
karatsuba [] ys = []
karatsuba xs [] = []
karatsuba xs ys = karatsuba' ((length xs) Data.Nat.⊔ (length ys)) xs ys




--------------------------
---------------   in progress


{-
*p-comm : ∀ (xs ys : List ℤ)
  → xs *p ys ≡ ys *p xs 
*p-comm ys [] = *pRightEmpty ys
*p-comm [] xs rewrite *pRightEmpty xs = refl 
*p-comm (x ∷ []) (y ∷ []) rewrite *-comm x y = refl 
*p-comm (x1 ∷ x2 ∷ xs) (y ∷ [])  rewrite *-comm x1 y | +-identityʳℤ (x2 * y) | *-comm x2 y | +pLeftEmpty (xs *p [ y ]) | *p-comm xs [ y ] | *p-map-left-single y xs = refl
*p-comm (x ∷ []) (y1 ∷ y2 ∷ ys)  rewrite *-comm x y1 | +-identityʳℤ (x * y2) | *-comm x y2 | +-identityʳℤ (y2 * x) | sym (*p-map-left-single x ys) | *p-comm ys [ x ] | +pLeftEmpty ([ x ] *p ys) = refl  
*p-comm (x1 ∷ x2 ∷ xs) (y1 ∷ y2 ∷ ys)   =  {!!}
-}{-
  begin
    (x1 ∷ x2 ∷ xs) (y1 ∷ y2 ∷ ys)
-}


assumption : ∀ (xs ys : List ℤ)
  → (xs +p ys) -p ys ≡ xs
assumption xs ys = {!!}

lengths : ∀ (a b c d : List ℤ)
  → 0 < length a
  → 0 < length b
  → 0 < length c
  → 0 < length d
  → length (a *p c)  ≤ length ((a *p d) +p (b *p c) ) 
lengths a b c d z<a z<b z<c z<d rewrite x+y≡x⊔y (a *p d) (b *p c) = {!!} --| m⊔n≤m+n (length (a *p d)) (length (b *p c)) = ? --|  length-*p ? ? ? ?    = ? 


testone : ∀ (a b c d : List ℤ)
  → 0 < length a
  → 0 < length b
  → 0 < length c
  → 0 < length d
  → ((a +p b) *p (c +p d)) -p (a *p c) ≡ ((a *p d) +p (b *p c)) +p (b *p d) 
testone a b c d rewrite sym (*p-+p-distrib-l (a +p b) c d) | +p-comm ((a +p b) *p c) ((a +p b) *p d) | +p-assoc  ((a +p b) *p d) ((a +p b) *p c) (negPoly (a *p c)) |  sym (*p-+p-distrib-r a b c) | +p-comm (a *p c) (b *p c) | +p-assoc  (b *p c)  (a *p c) (negPoly (a *p c)) | negPoly-lemma  (a *p c)  | sym (*p-+p-distrib-r a b d) = {!!} 



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
  ≡⟨ cong (_+p negPoly (ys *p rs)) (cong (((ys *p zs) +p (xs *p rs)) +p_) (assumption (ys *p rs) (xs *p zs)))  ⟩
     ((((ys *p zs) +p (xs *p rs)) +p (ys *p rs)) +p negPoly (ys *p rs))
   ≡⟨ assumption ((ys *p zs) +p (xs *p rs)) (ys *p rs)  ⟩
     (ys *p zs) +p (xs *p rs)
   ≡⟨ +p-comm (ys *p zs) (xs *p rs) ⟩
     (xs *p rs) +p (ys *p zs)
   ∎

half : ∀ (n : ℕ)
  → n / 2 ≤ n
half n  =  m/n≤m n  2


returnmin-left : ∀ (m n : ℕ)
  → m < n
  → m ⊓ n ≡ m
returnmin-left zero n m<n = refl
returnmin-left (ℕ.suc m) (ℕ.suc n) (s<s m<n) rewrite returnmin-left m n m<n = refl

returnmin-right : ∀ (m n : ℕ)
  → n < m
  → m ⊓ n ≡ n
returnmin-right (suc m) zero m<n = refl
returnmin-right (ℕ.suc m) (ℕ.suc n) (s<s m<n) rewrite returnmin-right m n m<n = refl 


a2<n⇒0<n : ∀ (n : ℕ)
  → 2 < n
  → 0 < n
a2<n⇒0<n  n two<n = Data.Nat.Properties.≤-trans  z<s two<n 
{-
ismul' : ∀ (n : ℕ) (xs ys : List ℤ)
  → xs *p ys ≡ karatsuba' n xs ys  
ismul' zero xs ys = refl    
ismul' (suc n) xs ys with (((length xs / 2) ⊓ (length ys / 2)) ≤ᵇ' 2)
...                   | true = refl
...                   | false =
                         begin
                           xs *p ys
                         ≡⟨ cong₂ (_*p_) (split-p-new  m xs ({!!})) (split-p-new  m ys ({!!})) ⟩  -- 1
                           (b +p shiftRight m a) *p (d +p shiftRight m c)
                         ≡⟨ sym (*p-+p-distrib-r b (shiftRight m a) (d +p shiftRight m c)) ⟩ -- 2
                           (b *p (d +p shiftRight m c)) +p ((shiftRight m a) *p (d +p shiftRight m c))
                         ≡⟨ cong₂ (_+p_) (sym (*p-+p-distrib-l b d (shiftRight m c))) (sym (*p-+p-distrib-l (shiftRight m a) d (shiftRight m c))) ⟩
                            ((b *p d) +p (b *p (shiftRight m c))) +p (((shiftRight m a) *p d) +p (shiftRight m a *p shiftRight m c))
                         ≡⟨ +p-rearrange (b *p d) (b *p (shiftRight m c)) ((shiftRight m a) *p d)  (shiftRight m a *p shiftRight m c) ⟩          
                           ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p (shiftRight m a *p shiftRight m c)
                         ≡⟨ cong (((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p_) (shiftRight-two-m m a c  {!!} {!!}  ) ⟩ -- 3
                           ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p (shiftRight (2 *ℕ m) (a *p c))       
                         ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c))) (cong ((b *p d) +p_) (cong (_+p ((shiftRight m a) *p d)) (*p-comm b (shiftRight m c)))) ⟩
                           ((b *p d) +p (((shiftRight m c) *p b) +p ((shiftRight m a) *p d))) +p (shiftRight (2 *ℕ m) (a *p c))   
                        ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c))) (cong ((b *p d) +p_) (cong₂ (_+p_) (sym (shiftRight-*p m c b {!!} {!!})) (sym (shiftRight-*p m a d {!!} {!!})))) ⟩ -- 4
                        ---------------
                           ((b *p d) +p ((shiftRight m (c *p b)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))

                        ≡⟨ cong (λ x → ((b *p d) +p ((shiftRight m (x)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))) (*p-comm c b)  ⟩
                           ((b *p d) +p ((shiftRight m (b *p c)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))
                        ≡⟨ cong (λ x → ((b *p d) +p (x)) +p (shiftRight (2 *ℕ m) (a *p c))) (+p-comm (shiftRight m (b *p c)) (shiftRight m (a *p d))) ⟩
                           ((b *p d) +p ((shiftRight m (a *p d)) +p (shiftRight m (b *p c)))) +p (shiftRight (2 *ℕ m) (a *p c))
                           
                        ≡⟨ cong (λ x → ((b *p d) +p  x)  +p (shiftRight (2 *ℕ m) (a *p c)))  (sym (shiftRight-+p  m _ _))  ⟩ -- 6
                         
                            ((b *p d) +p (shiftRight m ((a *p d) +p (b *p c)) )) +p (shiftRight (2 *ℕ m) (a *p c))
                            
                        ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c)))  ( cong (_+p (shiftRight m ((a *p d) +p (b *p c)) )) (ismul' n b d)) ⟩
                        
                            ((bd) +p (shiftRight m ((a *p d) +p (b *p c)))) +p (shiftRight (2 *ℕ m) (a *p c))
                            
                        ≡⟨ cong (λ x →  ((bd) +p (shiftRight m x)) +p (shiftRight (2 *ℕ m) (a *p c))) helperEq ⟩ --5,6     ad+bc-two a d b c
                        
                            ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))
                            
                        ≡⟨ cong (( bd +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))))  +p_)  (cong₂ shiftRight refl (ismul' n a  c) )  ⟩ --recursive call
                        
                           ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))))  +p (shiftRight (2 *ℕ m) (ac))
                           
                        ≡⟨ cong (_+p  (shiftRight ( 2 *ℕ m) (ac))) (cong (bd +p_) (cong₂ (_-p_) (cong₂ shiftRight refl (ismul' n (a +p b) (c +p d))) (ismul' n b d))) ⟩
                           ((bd) +p (shiftRight m ((((karatsuba' n (a +p b) (c +p d)) -p ac) -p bd)))) +p (shiftRight (2 *ℕ m) (ac))
                        ≡⟨⟩
                           ((bd) +p (shiftRight m (ad_plus_bc))) +p (shiftRight (2 *ℕ m) (ac))
                         ≡⟨ +p-assoc (bd) (shiftRight m (ad_plus_bc)) (shiftRight (2 *ℕ m) (ac)) ⟩
                           (bd) +p ((shiftRight m (ad_plus_bc)) +p (shiftRight (2 *ℕ m) (ac)))
                         ≡⟨ cong (bd +p_) (+p-comm (shiftRight m (ad_plus_bc))  (shiftRight (2 *ℕ m) (ac))) ⟩
                            bd +p ((shiftRight (2 *ℕ m) (ac)) +p (shiftRight m (ad_plus_bc)))
                         ≡⟨ +p-comm bd  ((shiftRight (2 *ℕ m) (ac)) +p (shiftRight m (ad_plus_bc))) ⟩
                           ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd
                         ∎
                           where
                           open Pair
                           m = ((length xs / 2) ⊓ (length ys / 2))
                           b = splitAt m xs .fst
                           a = splitAt m xs .snd
                           d = splitAt m ys .fst
                           c =  splitAt m ys .snd
                           ac = karatsuba' n a c 
                           bd = karatsuba' n b d
                           ad_plus_bc = ((karatsuba' n (a +p b) (c +p d) -p ac) -p bd)

                           helperEq : (a *p d) +p (b *p c) ≡  (((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d)
                           helperEq = {!!}                           

-}
module _ (*p-comm : (xs ys : List ℤ) → xs *p ys ≡ ys *p xs )  where   --- assuming commutativity for *p
  ismul'' : ∀ (n : ℕ) (xs ys : List ℤ)
    → xs *p ys ≡ karatsuba'' n xs ys
  ismul'' zero xs ys = refl
  ismul'' (ℕ.suc n) xs ys with (((length xs / 2) ⊓ (length ys / 2)) ≤? 2)
  ...                   | (yes _) = refl
  ...                   | (no ¬m≤2) = --{!m>2!}
    begin
      xs *p ys
                         ≡⟨ cong₂ (_*p_) (split-p  m xs m≤xs) (split-p  m ys m≤ys) ⟩
                         
                           (b +p shiftRight m a) *p (d +p shiftRight m c)
                           
                         ≡⟨ sym (*p-+p-distrib-r b (shiftRight m a) (d +p shiftRight m c)) ⟩
                         
                           (b *p (d +p shiftRight m c)) +p ((shiftRight m a) *p (d +p shiftRight m c))
                           
                         ≡⟨ cong₂ (_+p_) (sym (*p-+p-distrib-l b d (shiftRight m c))) (sym (*p-+p-distrib-l (shiftRight m a) d (shiftRight m c))) ⟩
                         
                            ((b *p d) +p (b *p (shiftRight m c))) +p (((shiftRight m a) *p d) +p (shiftRight m a *p shiftRight m c))
                            
                         ≡⟨ +p-rearrange (b *p d) (b *p (shiftRight m c)) ((shiftRight m a) *p d)  (shiftRight m a *p shiftRight m c) ⟩
                         
                           ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p (shiftRight m a *p shiftRight m c)
                           
                         ≡⟨ cong (((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p_) (shiftRight-two-m m a c  {!!} {!!}  ) ⟩ -- 3
                         
                           ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p (shiftRight (2 *ℕ m) (a *p c))
                           
                         ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c))) (cong ((b *p d) +p_) (cong (_+p ((shiftRight m a) *p d)) (*p-comm b (shiftRight m c)))) ⟩
                         
                           ((b *p d) +p (((shiftRight m c) *p b) +p ((shiftRight m a) *p d))) +p (shiftRight (2 *ℕ m) (a *p c))
                           
                        ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c))) (cong ((b *p d) +p_)
                        (cong₂ (_+p_) (sym (shiftRight-*p m c b {!!} (a2<n⇒0<n (length b) lb>2))) (sym (shiftRight-*p m a d {!!} (a2<n⇒0<n (length d) ld>2))))) ⟩
                        
                           ((b *p d) +p ((shiftRight m (c *p b)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))
                        
                        ≡⟨ cong (λ x → ((b *p d) +p ((shiftRight m (x)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))) (*p-comm c b)  ⟩
                        
                           ((b *p d) +p ((shiftRight m (b *p c)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))
                           
                        ≡⟨ cong (λ x → ((b *p d) +p (x)) +p (shiftRight (2 *ℕ m) (a *p c))) (+p-comm (shiftRight m (b *p c)) (shiftRight m (a *p d))) ⟩
                        
                           ((b *p d) +p ((shiftRight m (a *p d)) +p (shiftRight m (b *p c)))) +p (shiftRight (2 *ℕ m) (a *p c))
                           
                        ≡⟨ cong (λ x → ((b *p d) +p  x)  +p (shiftRight (2 *ℕ m) (a *p c)))  (sym (shiftRight-+p  m _ _))  ⟩ 
                        
                            ((b *p d) +p (shiftRight m ((a *p d) +p (b *p c)) )) +p (shiftRight (2 *ℕ m) (a *p c))
                            
                        ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c)))  ( cong (_+p (shiftRight m ((a *p d) +p (b *p c)) )) (ismul'' n b d)) ⟩
                        
                            ((bd) +p (shiftRight m ((a *p d) +p (b *p c)))) +p (shiftRight (2 *ℕ m) (a *p c))
                            
                        ≡⟨ cong (λ x →  ((bd) +p (shiftRight m x)) +p (shiftRight (2 *ℕ m) (a *p c))) {!!} ⟩ --5,6     ad+bc-two a d b c
                        
                            ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))
                            
                        ≡⟨ cong (( bd +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))))  +p_)  (cong₂ shiftRight refl (ismul'' n a  c) )  ⟩ 
                        
                           ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))))  +p (shiftRight (2 *ℕ m) (ac))
                           
                        ≡⟨ cong (λ x → ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (x))))  +p (shiftRight (2 *ℕ m) (ac))) (ismul'' n b d) ⟩
                        
                           ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))
                           
                        ≡⟨ cong (λ x → ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (x)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))) (ismul'' n a c) ⟩
                        
                           ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (ac)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))
                           
                        ≡⟨ cong (λ x → ((bd) +p (shiftRight m (((x) -p (ac)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))) (ismul'' n (a +p b) (c +p d)) ⟩
                        
                           ((bd) +p (shiftRight m ((((karatsuba'' n (a +p b) (c +p d)) -p ac) -p bd)))) +p (shiftRight (2 *ℕ m) (ac))
                        ≡⟨⟩
                           ((bd) +p (shiftRight m (ad_plus_bc))) +p (shiftRight (2 *ℕ m) (ac))
                           
                         ≡⟨ +p-assoc (bd) (shiftRight m (ad_plus_bc)) (shiftRight (2 *ℕ m) (ac)) ⟩
                         
                           (bd) +p ((shiftRight m (ad_plus_bc)) +p (shiftRight (2 *ℕ m) (ac)))
                           
                         ≡⟨ cong (bd +p_) (+p-comm (shiftRight m (ad_plus_bc))  (shiftRight (2 *ℕ m) (ac))) ⟩
                         
                            bd +p ((shiftRight (2 *ℕ m) (ac)) +p (shiftRight m (ad_plus_bc)))
                            
                         ≡⟨ +p-comm bd  ((shiftRight (2 *ℕ m) (ac)) +p (shiftRight m (ad_plus_bc))) ⟩
                         
                           (((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd )
                         ≡⟨⟩
                           {!!}
                         
    where
    open Pair
    m = ((length xs / 2) ⊓ (length ys / 2))
    b = take m xs 
    a = drop m xs
    d = take m ys
    c =  drop m ys
    ac = karatsuba'' n a c 
    bd = karatsuba'' n b d
    ad_plus_bc = ((karatsuba'' n (a +p b) (c +p d) -p ac) -p bd)
    m>2 : 2 < m
    m>2 = ≰⇒> ¬m≤2 


  
    shiftRight-two-m : ∀ (m : ℕ) (xs ys : List ℤ)      ---------- needs *p-comm, so this function is here and not in the library
      → zero < length xs
      → zero < length ys
      → shiftRight m xs *p shiftRight m ys ≡ shiftRight (2 Data.Nat.* m) (xs *p ys)
    shiftRight-two-m zero xs ys z<xs z<ys = refl
    shiftRight-two-m (ℕ.suc m) xs ys z<xs z<ys =
      begin
      (shiftRight (ℕ.suc m) xs) *p (shiftRight (ℕ.suc m) ys)
      ≡⟨ sym (shiftRight-*p (ℕ.suc m) xs (shiftRight (ℕ.suc m) ys) z<xs Data.Nat.z<s) ⟩
        shiftRight (ℕ.suc m) (xs *p shiftRight (ℕ.suc m) ys)
      ≡⟨ cong₂ shiftRight (refl) (*p-comm xs (shiftRight (ℕ.suc m) ys)) ⟩
        shiftRight (ℕ.suc m) ((shiftRight (ℕ.suc m) ys) *p xs)
      ≡⟨ cong₂ shiftRight (refl)(sym (shiftRight-*p (ℕ.suc m) ys xs z<ys z<xs)) ⟩ 
        shiftRight (ℕ.suc m) ((shiftRight (ℕ.suc m) (ys *p xs)))
      ≡⟨ shiftRight-shiftRight (ℕ.suc m) (ℕ.suc m) (ys *p xs) ⟩
        +0 ∷ shiftRight (m + ℕ.suc m) (ys *p xs) 
      ≡⟨ cong (+0 ∷_) (cong₂ shiftRight (cong (m +_) (cong ℕ.suc (sym (Data.Nat.Properties.+-identityʳ m)))) (*p-comm ys xs)) ⟩
        +0 ∷ shiftRight (m + suc (m + zero )) (xs *p ys)
      ∎


    m≤xs : m ≤ length xs
    m≤xs  with length xs / 2 ≤? length ys / 2
    ...                                       | (yes m≤n) rewrite Data.Nat.Properties.m≤n⇒m⊓n≡m m≤n = m/n≤m (length xs) 2   
    ...                                       | (no n<m) = (Data.Nat.Properties.m≤n⇒m⊓o≤n ((length ys) / 2) (m/n≤m (length xs) 2))
  
    m≤ys : m ≤ length ys
    m≤ys  with length ys / 2 ≤? length xs / 2
    ...                                       | (yes m≤n)   rewrite Data.Nat.Properties.m≥n⇒m⊓n≡n m≤n = m/n≤m (length ys) 2   
    ...                                       | (no n<m) = (Data.Nat.Properties.m≤n⇒o⊓m≤n ((length xs) / 2) (m/n≤m (length ys) 2))
  

    test : ∀ {m n o : ℕ} → m ≤ o → n ≤ o → (m ⊓ n) ⊓  o ≡ m ⊓ n 
    test  {zero} _ _    =  refl --Data.Nat.Properties.m≤n⇒m⊔n≡n n≤o 
    test {suc m} {zero} _ z≤o = refl  --cong suc (m≤n⇒m⊔n≡n m≤n)
    test  {suc m} {suc n} {suc o} (s≤s m≤o) (s≤s n≤o) = cong ℕ.suc (test  m≤o n≤o)


    lengthTakeMin : ∀ (m n : ℕ) (xs : List ℤ)
      → m ⊓ n ≤ length xs
      → length (take (m ⊓ n) xs) ≡ m ⊓ n 
    lengthTakeMin m n xs  m⊓n≤xs  rewrite length-take (m ⊓ n) xs | Data.Nat.Properties.m≤n⇒m⊓n≡m m⊓n≤xs = refl 

    lengthDropMin : ∀ (m n : ℕ) (xs : List ℤ)
      → m ⊓ n ≤ length xs
      → length (drop (m ⊓ n) xs) ≡ (length xs) Data.Nat.∸ m ⊓ n 
    lengthDropMin m n xs  m⊓n≤xs rewrite length-drop (m ⊓ n) xs = refl    --rewrite length-take (m ⊓ n) xs | Data.Nat.Properties.m≤n⇒m⊓n≡m m⊓n≤xs = refl 

    testfive : ∀ (m n : ℕ)
      → 2 < ((m / 2) ⊓ (n / 2) )
      → 5 < m
    testfive m n m/2⊓n/2>2 = {!!} 

    testsix : ∀ (m n : ℕ)
      → 5 < m
      → 2 < (m / 2)  ⊓ (n / 2)
      → 3 ≤ m ∸ ((m / 2)  ⊓ (n / 2))
    testsix m n m>5 m/2n/2>2 = {!!} 

  
    xs>5 : 5 < length xs
    xs>5  = testfive (length xs) (length ys) (≰⇒> ¬m≤2) -- rewrite m≤n⇒m⊓n≡m m≤n   = {!!} -- = {!!} --rewrite  Data.Nat.Properties.m≤n⇒m⊓n≡m  xs<ys = {!!} 

  
    lb>2 : 2 < length b
    lb>2  rewrite length-take m b | lengthTakeMin (length xs / 2) (length ys / 2) xs  (Data.Nat.Properties.m≤n⇒m⊓o≤n ((length ys) / 2) (m/n≤m (length xs) 2)) =  ≰⇒> ¬m≤2
  
    ld>2 : 2 < length d
    ld>2 rewrite length-take m d  | lengthTakeMin (length xs / 2) (length ys / 2) ys  (Data.Nat.Properties.m≤n⇒o⊓m≤n ((length xs) / 2) (m/n≤m (length ys) 2)) = ≰⇒> ¬m≤2 

    la>2 : length a > 2
    la>2 rewrite length-drop m a |  lengthDropMin (length xs / 2) (length ys / 2) xs ((Data.Nat.Properties.m≤n⇒m⊓o≤n ((length ys) / 2) (m/n≤m (length xs) 2))) = testsix (length xs) (length ys) (xs>5) ((≰⇒> ¬m≤2)) --| ∸-distribˡ-⊓-⊔ (length xs) (length xs / 2) (length ys / 2) = {!!} --= {!!} --divmod

    lc>2 : 2 < length c
    lc>2 = {!!}
  
