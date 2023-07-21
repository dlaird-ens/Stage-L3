{-# OPTIONS --cubical #-}

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path

SubstPathRight : {A : Type} {x y z : A} (p : x ≡ y) → (q : y ≡ z) → (t : y ≡ z) → (q ≡ t) 
  → (p ∙ q ≡ p ∙ t)

SubstPathRight p q t H i j = (p ∙ (H i)) j

SubstPathLeft : {A : Type} {x y z : A} (p : x ≡ y) → (q : x ≡ y) → (t : y ≡ z) → (p ≡ q) 
  → (p ∙ t ≡ q ∙ t)

SubstPathLeft p q t H i j =  ((H i) ∙ t) j     

RightMult : {A : Type} {x y z : A} (p : x ≡ y) → (t : x ≡ y) → (r : y ≡ z) → p ≡ t
  → (p ∙ r ≡ t ∙ r)

RightMult p t r H = λ i j → ((H i) ∙ r) j

InvProd : {A : Type} {x z : A} (y : A) → (p : x ≡ y) → (q : y ≡ z) 
  → sym (p ∙ q) ≡ (sym q) ∙ (sym p)

InvProd y p q = J (λ y r → sym (p ∙ r) ≡ (sym r) ∙ (sym p))  (J (λ y r → sym (r ∙ refl) ≡ (sym refl) ∙ (sym r)) refl p) q 

RightMultWithRefl : {A : Type} {x y z : A} (p : x ≡ y) → (q : y ≡ x) → (p ∙ q ≡ refl)
  → (p ≡ sym q) 

RightMultWithRefl p q H =
  p ≡⟨ (rUnit p) ⟩ 
  p ∙ refl ≡⟨ SubstPathRight p refl (q ∙ (sym q)) (sym (rCancel q)) ⟩ 
  p ∙ (q ∙ (sym q)) ≡⟨ assoc p q (sym q) ⟩ 
  (p ∙ q)  ∙ (sym q) ≡⟨ RightMult (p ∙ q) refl (sym q) H ⟩ 
  refl ∙ (sym q) ≡⟨ sym (lUnit (sym q)) ⟩ 
  (sym q) ∎

RightSimpl : {A : Type} {x y z : A} (p : x ≡ y) → (q : y ≡ z) → (t : x ≡ y) → (r : y ≡ z) 
  → (p ∙ q ≡ t ∙ r) 
  →  p ∙ q ∙ (sym r) ≡ t
 
RightSimpl p q t r H = 
  p ∙ q ∙ (sym r) ≡⟨ assoc p q (sym r) ⟩
  (p ∙ q) ∙ (sym r) ≡⟨ (RightMult (p ∙ q) (t ∙ r) (sym r) H) ⟩
  (t ∙ r) ∙ (sym r) ≡⟨ (sym (assoc t r (sym r))) ⟩
  t ∙ r ∙ (sym r) ≡⟨ (SubstPathRight t (r ∙ (sym r)) refl (rCancel r)) ⟩
  t ∙ refl ≡⟨ sym (rUnit t) ⟩  
  t ∎

RightSimplWithRefl : {A : Type} {x y z : A} (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) 
  → (p ∙ q ≡ r) 
  → (p ∙ q) ∙ (sym r) ≡ refl

RightSimplWithRefl p q r H =  
  (p ∙ q) ∙ (sym r) ≡⟨ (RightMult (p ∙ q) r (sym r) H) ⟩
  r ∙ (sym r) ≡⟨ rCancel r ⟩
  refl ∎    

Lemma1 : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (a₀₋ : a₀₀ ≡ a₀₁) → (a₁₋ : a₁₀ ≡ a₁₁) → (a₋₀ : a₀₀ ≡ a₁₀) → (a₋₁ : a₀₁ ≡ a₁₁) 
  → Square a₀₋ a₁₋ a₋₀ a₋₁ 
  → ((a₀₋ ∙ a₋₁) ∙ (sym (a₋₀ ∙ a₁₋)) ≡ refl)

Lemma1 p q r s fill = RightSimplWithRefl p s (r ∙ q) (sym (Square→compPath fill)) 

Lemma2 : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (p : a₀₀ ≡ a₀₁) → (q : a₁₀ ≡ a₁₁) → (r : a₀₀ ≡ a₁₀) → (s : a₀₁ ≡ a₁₁) 
  → ((p ∙ s) ∙ (sym (r ∙ q)) ≡ refl)
  → p ∙ s ∙ sym q ∙ sym r ≡ refl

Lemma2 p q r s H = 
  p ∙ s ∙ sym q ∙ sym r ≡⟨ assoc p s (sym q ∙ sym r) ⟩
  (p ∙ s) ∙ (sym q) ∙ (sym r) ≡⟨ (SubstPathRight (p ∙ s) ((sym q) ∙ (sym r)) (sym (r ∙ q)) (sym (InvProd _ r q))) ⟩
  (p ∙ s) ∙ (sym (r ∙ q)) ≡⟨ H ⟩ 
  refl ∎ 


SquareToReflPath : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (a₀₋ : a₀₀ ≡ a₀₁) → (a₁₋ : a₁₀ ≡ a₁₁) → (a₋₀ : a₀₀ ≡ a₁₀) → (a₋₁ : a₀₁ ≡ a₁₁) 
  → Square a₀₋ a₁₋ a₋₀ a₋₁ 
  → (a₀₋ ∙ a₋₁  ∙ (sym a₁₋) ∙ (sym a₋₀) ≡ refl)

SquareToReflPath p q r s fill = Lemma2 p q r s (Lemma1 p q r s fill)  

Lemma2bis1 : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (p : a₀₀ ≡ a₀₁) → (q : a₁₀ ≡ a₁₁) → (r : a₀₀ ≡ a₁₀) → (s : a₀₁ ≡ a₁₁) 
  → p ∙ s ∙ sym q ∙ sym r ≡ refl
  → p ∙ s ∙ (sym q) ≡ r  

Lemma2bis1 p q r s H = 
  p ∙ s ∙ (sym q) ≡⟨ rUnit (p ∙ s ∙ (sym q))  ⟩
  (p ∙ s ∙ (sym q)) ∙ refl ≡⟨ SubstPathRight ((p ∙ s ∙ (sym q))) refl ((sym r) ∙ r) (sym (lCancel r)) ⟩
  (p ∙ s ∙ (sym q)) ∙ (sym r) ∙ r ≡⟨ assoc _ _ _ ⟩
  ((p ∙ s ∙ (sym q)) ∙ (sym r)) ∙ r ≡⟨ refl ⟩ 
  ((p ∙ (s ∙ (sym q))) ∙ (sym r)) ∙ r ≡⟨ SubstPathLeft  ((p ∙ (s ∙ (sym q))) ∙ (sym r)) (p ∙ (s ∙ (sym q)) ∙ (sym r)) r (sym (assoc p (s ∙ (sym q)) (sym r))) ⟩
  (p ∙ (s ∙ (sym q)) ∙ (sym r)) ∙ r ≡⟨ SubstPathLeft (p ∙ (s ∙ (sym q)) ∙ (sym r)) (p ∙ s ∙ (sym q) ∙ (sym r)) r (SubstPathRight p ((s ∙ (sym q)) ∙ (sym r)) (s ∙ (sym q) ∙ (sym r)) (sym (assoc s (sym q) (sym r)))) ⟩
  (p ∙ s ∙ (sym q) ∙ (sym r)) ∙ r ≡⟨ SubstPathLeft (p ∙ s ∙ (sym q) ∙ (sym r)) refl r H ⟩
  refl ∙ r ≡⟨ sym (lUnit r) ⟩    
  r ∎

Lemma2bis2 : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (p : a₀₀ ≡ a₀₁) → (q : a₁₀ ≡ a₁₁) → (r : a₀₀ ≡ a₁₀) → (s : a₀₁ ≡ a₁₁)
  → p ∙ s ∙ (sym q) ≡ r
  → (p ∙ s ≡ r ∙ q)

Lemma2bis2 p q r s H = 
  p ∙ s ≡⟨ rUnit (p ∙ s) ⟩
  (p ∙ s) ∙ refl ≡⟨ SubstPathRight (p ∙ s) refl ((sym q) ∙ q) (sym (lCancel q)) ⟩
  (p ∙ s) ∙ (sym q) ∙ q ≡⟨ assoc _ _ _ ⟩
  ((p ∙ s) ∙ (sym q)) ∙ q  ≡⟨ SubstPathLeft ((p ∙ s) ∙ (sym q)) (p ∙ s ∙ (sym q)) q (sym (assoc _ _ _)) ⟩
  (p ∙ s ∙ (sym q)) ∙ q  ≡⟨ SubstPathLeft (p ∙ s ∙ (sym q)) r q H ⟩
  r ∙ q ∎ 

Lemma2bis : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (p : a₀₀ ≡ a₀₁) → (q : a₁₀ ≡ a₁₁) → (r : a₀₀ ≡ a₁₀) → (s : a₀₁ ≡ a₁₁)
  → p ∙ s ∙ sym q ∙ sym r ≡ refl 
  → (p ∙ s ≡ r ∙ q) 
Lemma2bis p q r s H = Lemma2bis2 p q r s (Lemma2bis1 p q r s H)
    
Lemma1bis : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (a₀₋ : a₀₀ ≡ a₀₁) → (a₁₋ : a₁₀ ≡ a₁₁) → (a₋₀ : a₀₀ ≡ a₁₀) → (a₋₁ : a₀₁ ≡ a₁₁) 
  → (a₀₋ ∙ a₋₁  ∙ (sym a₁₋) ∙ (sym a₋₀) ≡ refl)
  → Square a₀₋ a₁₋ a₋₀ a₋₁
Lemma1bis p q r s H = compPath→Square (sym (Lemma2bis p q r s H)) 

ReflPathToSquare : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → (a₀₋ : a₀₀ ≡ a₀₁) → (a₁₋ : a₁₀ ≡ a₁₁) → (a₋₀ : a₀₀ ≡ a₁₀) → (a₋₁ : a₀₁ ≡ a₁₁) 
  → (a₀₋ ∙ a₋₁  ∙ (sym a₁₋) ∙ (sym a₋₀) ≡ refl)
  → Square a₀₋ a₁₋ a₋₀ a₋₁

ReflPathToSquare p q r s H =  Lemma1bis p q r s H