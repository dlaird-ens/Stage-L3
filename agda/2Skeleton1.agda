{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}
 
open import HiTs
open import 1Skeleton
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.HITs.Pushout

open import 2SkeletonBase

private
  variable
    ℓ ℓ' : Level
    A : Type
    x y z : A
    a₀₀ a₀₁ a₁₀ a₁₁ : A
    b₀₀ b₀₁ b₁₀ b₁₁ : A


-- 2ème tentative avec des faces ponctuelles
data sides : Type where
  f1 : sides
  f3 : sides 
  f5 : sides

g : (triple Circle Circle Circle) → sides
g (i1 c₀₀) = f1
g (i1 c₀₁) = f1
g (i1 c₁₀) = f1
g (i1 c₁₁) = f1
g (i1 (c₀₋ i)) = f1
g (i1 (c₁₋ i)) = f1
g (i1 (c₋₀ i)) = f1
g (i1 (c₋₁ i)) = f1
g (i2 c₀₀) = f3
g (i2 c₀₁) = f3
g (i2 c₁₀) = f3
g (i2 c₁₁) = f3
g (i2 (c₀₋ i)) = f3
g (i2 (c₁₋ i)) = f3
g (i2 (c₋₀ i)) = f3
g (i2 (c₋₁ i)) = f3
g (i3 c₀₀) = f5
g (i3 c₀₁) = f5
g (i3 c₁₀) = f5
g (i3 c₁₁) = f5
g (i3 (c₀₋ i)) = f5
g (i3 (c₁₋ i)) = f5
g (i3 (c₋₀ i)) = f5
g (i3 (c₋₁ i)) = f5

2Sq = Pushout {A = (triple Circle Circle Circle)} {B = 1Sq} {C = sides} f g

isContrSquare :
  {ℓ : Level} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  (s : Square a₀₋ a₁₋ a₋₀ a₋₁)
  -- → isContr s
  (i j : I) → a₀₀ ≡ s i j
isContrSquare {a₀₀ = a₀₀} s i j k = s (i ∧ k) (j ∧ k)

ret2 : 2Sq → Hypercubic2

-- Correspondance des sommets
ret2 (inl (inl whiteV)) = whiteV
ret2 (inl (inr blueV)) = blueV

-- Correspondance entre les arêtes
ret2 (inl (push redE i)) = redE i
ret2 (inl (push blueE i)) = blueE i
ret2 (inl (push greenE i)) = greenE i
ret2 (inl (push yellowE i)) = yellowE i

ret2 (inr f1) = blueV
ret2 (inr f3) = blueV
ret2 (inr f5) = blueV

ret2 (push (i1 c₀₀) i) = blueV
ret2 (push (i1 c₀₁) i) = yellowE i
ret2 (push (i1 c₁₀) i) = blueE i
ret2 (push (i1 c₁₁) i) =  (sym blueE ∙ greenE ) i
ret2 (push (i1 (c₀₋ i)) j) = {!!}  yellowE ((~ i) ∨ j)
ret2 (push (i1 (c₁₋ i)) j) = {!!}
ret2 (push (i1 (c₋₀ i)) j) = {!!}
ret2 (push (i1 (c₋₁ i)) j) = {!!}
ret2 (push (i2 c₀₀) i) = blueV
ret2 (push (i2 c₀₁) i) = yellowE i
ret2 (push (i2 c₁₀) i) = redE i
ret2 (push (i2 c₁₁) i) = {!!}
ret2 (push (i2 (c₀₋ ₁)) j) = {!   !}
ret2 (push (i2 (c₁₋ i)) j) = {!   !}
ret2 (push (i2 (c₋₀ i)) j) = {!   !}
ret2 (push (i2 (c₋₁ i)) j) = {!   !}
ret2 (push (i3 c₀₀) i) = {!   !}
ret2 (push (i3 c₀₁) i) = {!   !}
ret2 (push (i3 c₁₀) i) = {!   !}
ret2 (push (i3 c₁₁) i) = {!   !}
ret2 (push (i3 (c₀₋ i)) j) = {!   !}
ret2 (push (i3 (c₁₋ i)) j) = {!   !}
ret2 (push (i3 (c₋₀ i)) j) = {!   !}
ret2 (push (i3 (c₋₁ i)) j) = {!   !}

inl12 : 1Sq → 2Sq
inl12 = inl

inr12 : sides → 2Sq
inr12 = inr

push12 : (x : triple Circle Circle Circle) → inl12 (f x) ≡ inr12 (g x)
push12 = push


lemme : {ℓ : Level} {A : Type ℓ} (f : Circle → A) (a : A) (p : (x : Circle) → a ≡ f x) → Square (cong f c₀₋) (cong f c₁₋) (cong f c₋₀) (cong f c₋₁)
lemme f aa p = λ i j → {!   !}

sf1 : Square
        {A = 2Sq}
        {inl (inr blueV)}
        {inl (inl whiteV)}
        (cong inl12 (sym (push yellowE)))
        {inl (inl whiteV)}
        {inl (inr blueV)}
        (cong inl12 (push greenE))
        (cong inl12 (sym (push blueE)))
        (cong inl12 (push redE))

path : (x : Circle) → (inr f1) ≡ ((inl12 ∘ f ∘ i1) x)
path c₀₀ = sym push i1 c₀₀
path c₀₁ = sym push i1 c₀₁
path c₁₀ = sym push i1 c₁₀
path c₁₁ = sym push i1 c₁₁
path (c₀₋ i) = sym push i1 c₁₋
path (c₁₋ i) = sym push i1 c₁₋
path (c₋₀ i) = sym push i1 c₋₀
path (c₋₁ i) = sym push i1 c₋₁

sf1 = lemme (inl12 ∘ f ∘ i1) (inr f1) path

sec2 : Hypercubic2 → 2Sq
{-Correspondance entre les sommets-}

sec2 blueV = inl(inr(blueV))
sec2 whiteV = inl(inl(whiteV))

{-Correspondanc entre les arêtes-}
sec2 (yellowE i) = inl(push yellowE i)
sec2 (greenE i) = inl(push greenE i)
sec2 (redE i) = inl (push redE i)
sec2 (blueE i) = inl (push blueE i)

{-Correspondance entre les remplissements des faces-}
sec2 (f1 i j) = sf1 i j
sec2 (f3 i j) = {!!}
sec2 (f5 i j) = {!!}






