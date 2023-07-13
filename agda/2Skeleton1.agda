{-# OPTIONS --cubical #-}

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
g (i1 (c₀₋ i)) = refl i
g (i1 (c₁₋ i)) = refl i
g (i1 (c₋₀ i)) = refl i
g (i1 (c₋₁ i)) = refl i
g (i2 c₀₀) = f3
g (i2 c₀₁) = f3
g (i2 c₁₀) = f3
g (i2 c₁₁) = f3
g (i2 (c₀₋ i)) = refl i
g (i2 (c₁₋ i)) = refl i
g (i2 (c₋₀ i)) = refl i
g (i2 (c₋₁ i)) = refl i
g (i3 c₀₀) = f5
g (i3 c₀₁) = f5
g (i3 c₁₀) = f5
g (i3 c₁₁) = f5
g (i3 (c₀₋ i)) = refl i
g (i3 (c₁₋ i)) = refl i
g (i3 (c₋₀ i)) = refl i
g (i3 (c₋₁ i)) = refl i

2Sq = Pushout {A = (triple Circle Circle Circle)} {B = 1Sq} {C = sides} f g

ret2 : 2Sq → Hypercubic2

-- Correspondance des sommets
ret2 (inl (inl whiteV)) = whiteV
ret2 (inl (inr blueV)) = blueV

-- Correspondance entre les arêtes
ret2 (inl (push redE i)) = redE i
ret2 (inl (push blueE i)) = blueE i
ret2 (inl (push greenE i)) = greenE i
ret2 (inl (push yellowE i)) = yellowE i

ret2 (inr f1) = {!!}
ret2 (inr f3) = {!   !}
ret2 (inr f5) = {!   !}

ret2 (push (i1 c₀₀) i) = {!   !}
ret2 (push (i1 c₀₁) i) = {!   !}
ret2 (push (i1 c₁₀) i) = {!   !}
ret2 (push (i1 c₁₁) i) = {!   !}
ret2 (push (i1 (c₀₋ i)) j) = {!   !}
ret2 (push (i1 (c₁₋ i)) j) = {!   !}
ret2 (push (i1 (c₋₀ i)) j) = {!   !}
ret2 (push (i1 (c₋₁ i)) j) = {!   !}
ret2 (push (i2 c₀₀) i) = {!   !}
ret2 (push (i2 c₀₁) i) = {!   !}
ret2 (push (i2 c₁₀) i) = {!   !}
ret2 (push (i2 c₁₁) i) = {!   !}
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
sec2 (f1 i j) = {!   !}
sec2 (f3 i j) = {!   !}
sec2 (f5 i j) = {!   !}
