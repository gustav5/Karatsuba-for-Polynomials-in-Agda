import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Nat renaming( _*_ to _*ℕ_) 
open import Data.Nat.Properties renaming(*-comm to *-commℕ)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer  using (ℤ;+0;_*_) renaming (_+_ to _+ℤ_; -_ to -i_) 
open import Data.Integer.Properties hiding(_≤?_;≰⇒>;_<?_;m≤n⇒m⊔n≡n;≤-reflexive;<⇒≤;m≤n⇒m⊓n≡m;≤-trans;m≥n⇒m⊓n≡n;m⊓n≤m;m≤m⊔n;m≤m+n) renaming (*-zeroʳ to *-zeroʳℤ;*-zeroˡ to *-zeroˡℤ;+-inverseʳ to +-inverseʳℤ; +-identityʳ to +-identityʳℤ;+-identityˡ to +-identityˡℤ;+-comm to +-commℤ;*-distribʳ-+ to *-distribʳ-+ℤ;*-distribˡ-+ to *-distribˡ-+ℤ;≤-refl to ≤-reflℤ;+-assoc to +-assocℤ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Level using (Level)
open import Data.Nat.DivMod 
open import Data.Empty using (⊥; ⊥-elim)
open import library 



--------------------------
--------------------------
-- Karatsuba

karatsuba' : ℕ → List ℤ → List ℤ → List ℤ
karatsuba' zero xs ys = xs *p ys
karatsuba' (suc n) xs ys with ((((length xs) / 2) ⊓ (length ys / 2)) ≤? 2)
...   | (yes _) = (xs *p ys)
...   | (no _) = ((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd
                       where
                       m = ((length xs / 2) ⊓ (length ys / 2)) 
                       b = take m xs
                       a = drop m xs
                       d  = take m ys
                       c = drop m ys 
                       ac = karatsuba' n a c  
                       bd = karatsuba' n b d 
                       ad_plus_bc = ((karatsuba' n (a +p b) (c +p d) -p ac) -p bd) 
                           
karatsuba : List ℤ → List ℤ → List ℤ
karatsuba [] ys = []
karatsuba xs [] = []
karatsuba xs ys = karatsuba' ((length xs) ⊔ (length ys)) xs ys


-- Proof 
module _ (assum : (m : ℕ)(a b c d : List ℤ) → ((shiftRight m ((a *p d) +p (b *p c)))+p (shiftRight (2 *ℕ m) (a *p c))) ≡  ((shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))) +p (shiftRight (2 *ℕ m) (a *p c))))
         ( m/2>2⇒5<m : ∀ (m : ℕ) → 2 < m / 2 → 5 < m)
         (drop-lemma :  (xs ys : List ℤ) → 5 < (length xs) → 5 < (length ys) → 3 ≤ length (drop ((length xs / 2) ⊓  (length ys / 2)) xs))
         (drop-lemma-two :  (xs ys : List ℤ) → 5 < (length xs) → 5 < (length ys) → 3 ≤ length (drop ((length xs / 2) ⊓  (length ys / 2)) ys)) where   
  ismul'' : ∀ (n : ℕ) (xs ys : List ℤ)
    → xs *p ys ≡ karatsuba' n xs ys
  ismul'' zero xs ys = refl
  ismul'' (suc n) xs ys with (((length xs / 2) ⊓ (length ys / 2)) ≤? 2)
  ...                   | (yes _) = refl
  ...                   | (no ¬m≤2) = 
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

       ≡⟨ cong (((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p_) (shiftRight-two-m m a c  (n>2⇒0<n (length a) la>2) (n>2⇒0<n (length c) lc>2)  ) ⟩ 

         ((b *p d) +p ((b *p (shiftRight m c)) +p ((shiftRight m a) *p d))) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c))) (cong ((b *p d) +p_) (cong (_+p ((shiftRight m a) *p d)) (*p-comm b (shiftRight m c)))) ⟩

         ((b *p d) +p (((shiftRight m c) *p b) +p ((shiftRight m a) *p d))) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c))) (cong ((b *p d) +p_)
       (cong₂ (_+p_) (sym (shiftRight-*p m c b ((n>2⇒0<n (length c) lc>2)) (n>2⇒0<n (length b) lb>2))) (sym (shiftRight-*p m a d (n>2⇒0<n (length a) la>2) (n>2⇒0<n (length d) ld>2))))) ⟩

          ((b *p d) +p ((shiftRight m (c *p b)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ cong (λ x → ((b *p d) +p ((shiftRight m (x)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))) (*p-comm c b)  ⟩

          ((b *p d) +p ((shiftRight m (b *p c)) +p (shiftRight m (a *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ cong (λ x → ((b *p d) +p (x)) +p (shiftRight (2 *ℕ m) (a *p c))) (+p-comm (shiftRight m (b *p c)) (shiftRight m (a *p d))) ⟩

          ((b *p d) +p ((shiftRight m (a *p d)) +p (shiftRight m (b *p c)))) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ cong (λ x → ((b *p d) +p  x)  +p (shiftRight (2 *ℕ m) (a *p c)))  (sym (shiftRight-+p  m _ _))  ⟩ 

           ((b *p d) +p (shiftRight m ((a *p d) +p (b *p c)) )) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ cong (_+p (shiftRight (2 *ℕ m) (a *p c)))  ( cong (_+p (shiftRight m ((a *p d) +p (b *p c)) )) (ismul'' n b d)) ⟩

           ((bd) +p (shiftRight m ((a *p d) +p (b *p c)))) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ +p-assoc (bd) (shiftRight m ((a *p d) +p (b *p c))) (shiftRight (2 *ℕ m) (a *p c)) ⟩

           (bd) +p ((shiftRight m ((a *p d) +p (b *p c)))+p (shiftRight (2 *ℕ m) (a *p c)))

       ≡⟨ cong (bd +p_) (assum m a b c d) ⟩ 

           ((bd) +p ((shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))) +p (shiftRight (2 *ℕ m) (a *p c))))

       ≡⟨ sym (+p-assoc (bd) (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))) (shiftRight (2 *ℕ m) (a *p c))) ⟩

          ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d)))) +p (shiftRight (2 *ℕ m) (a *p c))

       ≡⟨ cong (( bd +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))))  +p_)  (cong₂ shiftRight refl (ismul'' n a  c) )  ⟩ 

          ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (b *p d))))  +p (shiftRight (2 *ℕ m) (ac))

       ≡⟨ cong (λ x → ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (x))))  +p (shiftRight (2 *ℕ m) (ac))) (ismul'' n b d) ⟩

          ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (a *p c)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))

       ≡⟨ cong (λ x → ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (x)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))) (ismul'' n a c) ⟩

          ((bd) +p (shiftRight m ((((a +p b) *p (c +p d)) -p (ac)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))

       ≡⟨ cong (λ x → ((bd) +p (shiftRight m (((x) -p (ac)) -p (bd))))  +p (shiftRight (2 *ℕ m) (ac))) (ismul'' n (a +p b) (c +p d)) ⟩

          ((bd) +p (shiftRight m ((((karatsuba' n (a +p b) (c +p d)) -p ac) -p bd)))) +p (shiftRight (2 *ℕ m) (ac))
       ≡⟨⟩
          ((bd) +p (shiftRight m (ad_plus_bc))) +p (shiftRight (2 *ℕ m) (ac))

        ≡⟨ +p-assoc (bd) (shiftRight m (ad_plus_bc)) (shiftRight (2 *ℕ m) (ac)) ⟩

          (bd) +p ((shiftRight m (ad_plus_bc)) +p (shiftRight (2 *ℕ m) (ac)))

        ≡⟨ cong (bd +p_) (+p-comm (shiftRight m (ad_plus_bc))  (shiftRight (2 *ℕ m) (ac))) ⟩

           bd +p ((shiftRight (2 *ℕ m) (ac)) +p (shiftRight m (ad_plus_bc)))

        ≡⟨ +p-comm bd  ((shiftRight (2 *ℕ m) (ac)) +p (shiftRight m (ad_plus_bc))) ⟩

          (((shiftRight (2 *ℕ m) ac) +p (shiftRight m ad_plus_bc)) +p bd )
        ∎

    where
    open Pair
    m = ((length xs / 2) ⊓ (length ys / 2))
    b = take m xs 
    a = drop m xs
    d = take m ys
    c =  drop m ys
    ac = karatsuba' n a c 
    bd = karatsuba' n b d
    ad_plus_bc = ((karatsuba' n (a +p b) (c +p d) -p ac) -p bd)
    m>2 : 2 < m
    m>2 = ≰⇒> ¬m≤2 


    m≤xs : m ≤ length xs
    m≤xs  with length xs / 2 ≤? length ys / 2
    ...                                       | (yes m≤n) rewrite m≤n⇒m⊓n≡m m≤n = m/n≤m (length xs) 2   
    ...                                       | (no n<m) = (m≤n⇒m⊓o≤n ((length ys) / 2) (m/n≤m (length xs) 2))
  
    m≤ys : m ≤ length ys
    m≤ys  with length ys / 2 ≤? length xs / 2
    ...                                       | (yes m≤n)   rewrite m≥n⇒m⊓n≡n m≤n = m/n≤m (length ys) 2   
    ...                                       | (no n<m) = (m≤n⇒o⊓m≤n ((length xs) / 2) (m/n≤m (length ys) 2))
  

    m/2⊓n/2>2⇒5<m : ∀ (m n : ℕ)
      → 2 < ((m / 2) ⊓ (n / 2) )
      → 5 < m
    m/2⊓n/2>2⇒5<m m n m/2⊓n/2>2 = m/2>2⇒5<m  m (m≤n⊓o⇒m≤n (m / 2) (n / 2) m/2⊓n/2>2)

    m/2⊓n/2>2⇒5<n : ∀ (m n : ℕ)
      → 2 < ((m / 2) ⊓ (n / 2) )
      → 5 < n
    m/2⊓n/2>2⇒5<n m n m/2⊓n/2>2 = m/2>2⇒5<m  n (m≤n⊓o⇒m≤o (m / 2) (n / 2) m/2⊓n/2>2)

 
    xs>5 : 5 < length xs
    xs>5  = m/2⊓n/2>2⇒5<m (length xs) (length ys) (≰⇒> ¬m≤2) 
    
    ys>5 : 5 < length ys
    ys>5  = m/2⊓n/2>2⇒5<n   (length xs) (length ys) (≰⇒> ¬m≤2)
   

    lb>2 : 2 < length b
    lb>2  rewrite length-take m b | lengthTakeMin (length xs / 2) (length ys / 2) xs  (m≤n⇒m⊓o≤n ((length ys) / 2) (m/n≤m (length xs) 2)) =  ≰⇒> ¬m≤2
  
    ld>2 : 2 < length d
    ld>2 rewrite length-take m d  | lengthTakeMin (length xs / 2) (length ys / 2) ys  (m≤n⇒o⊓m≤n ((length xs) / 2) (m/n≤m (length ys) 2)) = ≰⇒> ¬m≤2 

    la>2 : length a > 2
    la>2 rewrite length-drop m a = drop-lemma xs ys xs>5 ys>5

    lc>2 : 2 < length c
    lc>2  rewrite length-drop m c = drop-lemma-two xs ys xs>5 ys>5 
  
    
