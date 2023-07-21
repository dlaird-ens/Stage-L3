{-# OPTIONS --cubical #-}


open import HiTs
open import 1Skeleton
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.HITs.Pushout
open import PathsLemmas


private
  variable
    A : Type
    B : Type 
    x y z : A
    a₀₀ a₀₁ a₁₀ a₁₁ : A
    b₀₀ b₀₁ b₁₀ b₁₁ : A 

{-On définit cette fois-ci le 2Sq par un Pushout-}
{-
                3S^1 -----------g-----------> sides
                  |                             |
                  |                             |
                  |                             |
                  |                             |
                  |                             i
                  f                             n
                  |                             r
                  |                             |
                  |                             |  
                  V                             V
                  1Sq------------inl---------->2Sq
-}

{- Le 2-squelette de la variété hypercubique -}

data Hypercubic2 : Type where 
    blueV : Hypercubic2
    whiteV : Hypercubic2
    yellowE : whiteV ≡ blueV 
    greenE : whiteV ≡ blueV 
    redE : whiteV ≡ blueV
    blueE : whiteV ≡ blueV
    f1 : Square (sym yellowE) greenE (sym blueE) redE
    f3 : Square (sym yellowE) blueE (sym redE) greenE
    f5 : Square (sym blueE) greenE (sym redE) yellowE

data triple (A : Type) (B : Type) (C : Type): Type where 
{-Réalise l'union disjointe de trois types-}
  i1 : A → triple A B C 
  i2 : B → triple A B C 
  i3 : C → triple A B C 

f : (triple S¹ S¹ S¹) → 1Sq
f (i1 base) = inr blueV
f (i1 (loop i)) = ((sym (push yellowE)) ∙ (push redE) ∙  (sym (push greenE)) ∙ (push blueE)) i
f (i2 base) = inr blueV
f (i2 (loop i)) = ((sym (push yellowE)) ∙ (push greenE) ∙ (sym (push blueE)) ∙ (push redE)) i
f (i3 base) = inr blueV
f (i3 (loop i)) = ((sym (push blueE)) ∙ (push yellowE) ∙ (sym (push greenE)) ∙ (push redE)) i  


data sides : Type where
    f1 : sides
    f3 : sides
    f5 : sides

g : (triple S¹ S¹ S¹) → sides
g (i1 base) = f1
g (i1 (loop i)) = f1
g (i2 base) = f3
g (i2 (loop i)) = f3
g (i3 base) = f5
g (i3 (loop i)) = f5 


2Sq = Pushout f g 

inl12 :  1Sq → 2Sq
inl12 = inl  

inr12 : sides → 2Sq 
inr12 = inr  

push12 : (x : (triple S¹ S¹ S¹)) → (inl12 ∘ f) x ≡ (inr12 ∘ g) x
push12 = push   

PathToReflPath : {A : Type} (x : A) → (y : A) → (x ≡ y) → ((λ (i : I) → x) ≡ (λ (i : I) → y)) 

PathToReflPath x y p i j = p i

HcongPaths : {A B : Type} (f : A → B) → (g : A → B) → (H : ((a : A) → (f a ≡ g a))) →  (x : A) → (y : A) → (p : x ≡ y) → (congS f p) ≡ (congS (λ x → H x i0) p)

HcongPaths f g H x y p i = congS f p 

test : (λ (i : I) → inr12 f1) ≡  (λ (i : I) → inl12 (inr01 blueV))
test = PathToReflPath (inr12 f1) (inl12 (inr01 blueV)) (sym (push12 (i1 base)))


test2 : congS f (congS i1 loop) ≡ ((sym (push yellowE)) ∙ (push redE) ∙  (sym (push greenE)) ∙ (push blueE))
test2 = refl 

{-
ret2 : 2Sq → Hypercubic2

ret2 (inl (inl whiteV)) = whiteV
ret2 (inl (inr blueV)) = blueV
ret2 (inl (push redE i)) = redE i
ret2 (inl (push blueE i)) = blueE i
ret2 (inl (push greenE i)) = greenE i
ret2 (inl (push yellowE i)) = yellowE i
ret2 (inr f1) = f1 i0 i0
ret2 (inr f3) = f3 i0 i0
ret2 (inr f5) = f5 i0 i0
ret2 (push (i1 base) i) = blueV
ret2 (push (i1 (loop i)) j) = {! !}
ret2 (push (i2 base) i) = blueV
ret2 (push (i2 (loop i)) j) = {!   !}
ret2 (push (i3 base) i) = blueV
ret2 (push (i3 (loop i)) j) = {!   !}

-}
{-
sec2 : Hypercubic2 → 2Sq

sec2 blueV = inl (inr blueV)
sec2 whiteV = inl (inl whiteV)
sec2 (yellowE i) = inl (push yellowE i)
sec2 (greenE i) = inl (push greenE i)
sec2 (redE i) = inl (push redE i)
sec2 (blueE i) = inl (push blueE i)
sec2 (f1 i j) =  {!   !}
sec2 (f3 i j) = {!   !}
sec2 (f5 i j) = {!   !}
-}
