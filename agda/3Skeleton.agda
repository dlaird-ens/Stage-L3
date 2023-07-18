{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import HiTs
open import 1Skeleton
open import 2SkeletonBase
open import 2Skeleton 
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.HITs.Pushout 

private
  variable
    ℓ ℓ' : Level
    A : Type
    x y z : A
    a₀₀ a₀₁ a₁₀ a₁₁ : A
    b₀₀ b₀₁ b₁₀ b₁₁ : A 

{-Dernier Pushout-}

data CubeBoundary : Type where
  a₀₀₀ : CubeBoundary
  a₀₀₁ : CubeBoundary
  a₀₁₀ : CubeBoundary
  a₀₁₁ : CubeBoundary
  a₁₀₀ : CubeBoundary
  a₁₀₁ : CubeBoundary
  a₁₁₀ : CubeBoundary
  a₁₁₁ : CubeBoundary
  a₀₀₋ : a₀₀₀ ≡ a₀₀₁
  a₀₁₋ : a₀₁₀ ≡ a₀₁₁
  a₀₋₀ : a₀₀₀ ≡ a₀₁₀
  a₀₋₁ : a₀₀₁ ≡ a₀₁₁
  a₁₀₋ : a₁₀₀ ≡ a₁₀₁
  a₁₁₋ : a₁₁₀ ≡ a₁₁₁
  a₁₋₀ : a₁₀₀ ≡ a₁₁₀
  a₁₋₁ : a₁₀₁ ≡ a₁₁₁
  a₋₀₀ : a₀₀₀ ≡ a₁₀₀
  a₋₀₁ : a₀₀₁ ≡ a₁₀₁
  a₋₁₀ : a₀₁₀ ≡ a₁₁₀
  a₋₁₁ : a₀₁₁ ≡ a₁₁₁
  a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁
  a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁
  a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁
  a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁
  a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀
  a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁

data Cubic : Type where 
  x₀₀₀ : Cubic
  x₀₀₁ : Cubic
  x₀₁₀ : Cubic
  x₀₁₁ : Cubic
  x₁₀₀ : Cubic
  x₁₀₁ : Cubic
  x₁₁₀ : Cubic
  x₁₁₁ : Cubic
  x₀₀₋ : x₀₀₀ ≡ x₀₀₁
  x₀₁₋ : x₀₁₀ ≡ x₀₁₁
  x₀₋₀ : x₀₀₀ ≡ x₀₁₀
  x₀₋₁ : x₀₀₁ ≡ x₀₁₁
  x₁₀₋ : x₁₀₀ ≡ x₁₀₁
  x₁₁₋ : x₁₁₀ ≡ x₁₁₁
  x₁₋₀ : x₁₀₀ ≡ x₁₁₀
  x₁₋₁ : x₁₀₁ ≡ x₁₁₁
  x₋₀₀ : x₀₀₀ ≡ x₁₀₀
  x₋₀₁ : x₀₀₁ ≡ x₁₀₁
  x₋₁₀ : x₀₁₀ ≡ x₁₁₀
  x₋₁₁ : x₀₁₁ ≡ x₁₁₁
  x₀₋₋ : Square x₀₀₋ x₀₁₋ x₀₋₀ x₀₋₁
  x₁₋₋ : Square x₁₀₋ x₁₁₋ x₁₋₀ x₁₋₁
  x₋₀₋ : Square x₀₀₋ x₁₀₋ x₋₀₀ x₋₀₁
  x₋₁₋ : Square x₀₁₋ x₁₁₋ x₋₁₀ x₋₁₁
  x₋₋₀ : Square x₀₋₀ x₁₋₀ x₋₀₀ x₋₁₀
  x₋₋₁ : Square x₀₋₁ x₁₋₁ x₋₀₁ x₋₁₁
  3cell : Cube x₀₋₋ x₁₋₋ x₋₀₋ x₋₁₋ x₋₋₀ x₋₋₁


{-On construit encore le 3-squelette par un pushout homotopique
Le pushout est le suivant:

                CubeBoundary -----k---------> cubic
                  |                             |
                  |                             |
                  |                             |
                  |                             |
                  |                             i
                  h                             n
                  |                             r
                  |                             |
                  |                             |  
                  V                             V
                  2Sq------------inl---------->3Sq

-}

k : CubeBoundary → Cubic
k a₀₀₀ = x₀₀₀
k a₀₀₁ = x₀₀₁
k a₀₁₀ = x₀₁₀
k a₀₁₁ = x₀₁₁
k a₁₀₀ = x₁₀₀
k a₁₀₁ = x₁₀₁
k a₁₁₀ = x₁₁₀
k a₁₁₁ = x₁₁₁
k (a₀₀₋ i) = x₀₀₋ i
k (a₀₁₋ i) = x₀₁₋ i
k (a₀₋₀ i) = x₀₋₀ i
k (a₀₋₁ i) = x₀₋₁ i
k (a₁₀₋ i) = x₁₀₋ i
k (a₁₁₋ i) = x₁₁₋ i
k (a₁₋₀ i) = x₁₋₀ i
k (a₁₋₁ i) = x₁₋₁ i
k (a₋₀₀ i) = x₋₀₀ i
k (a₋₀₁ i) = x₋₀₁ i
k (a₋₁₀ i) = x₋₁₀ i
k (a₋₁₁ i) = x₋₁₁ i
k (a₀₋₋ i j) = x₀₋₋ i j
k (a₁₋₋ i j) = x₁₋₋ i j
k (a₋₀₋ i j) = x₋₀₋ i j
k (a₋₁₋ i j) = x₋₁₋ i j
k (a₋₋₀ i j) = x₋₋₀ i j
k (a₋₋₁ i j) = x₋₋₁ i j



h : CubeBoundary → 2Sq
h a₀₀₀ = inl(inr(blueV))
h a₀₀₁ = inl(inl(whiteV))
h a₀₁₀ = inl(inl(whiteV))
h a₀₁₁ = inl(inr(blueV))
h a₁₀₀ = inl(inl(whiteV))
h a₁₀₁ = inl(inr(blueV))
h a₁₁₀ = inl(inr(blueV))
h a₁₁₁ = inl(inl(whiteV))
h (a₀₀₋ i) = inl(sym(push yellowE) i)
h (a₀₁₋ i) = inl(push greenE i)
h (a₀₋₀ i) = inl(sym(push blueE) i)
h (a₀₋₁ i) = inl(push redE i)
h (a₁₀₋ i) = inl(push blueE i)
h (a₁₁₋ i) = inl(sym(push redE) i)
h (a₁₋₀ i) = inl(push greenE i)
h (a₁₋₁ i) = inl(sym(push yellowE) i)
h (a₋₀₀ i) = inl(sym(push redE) i)
h (a₋₀₁ i) = inl(push greenE i)
h (a₋₁₀ i) = inl(push yellowE i)
h (a₋₁₁ i) = inl(sym(push blueE) i)
h (a₀₋₋ i j) = sf1 i j
h (a₁₋₋ i j) = (rot sf1) i j
h (a₋₀₋ i j) = sf3 i j
h (a₋₁₋ i j) = (anti-rot sf3) i j
h (a₋₋₀ i j) = sf5 i j
h (a₋₋₁ i j) = (rot sf5) i j 

3Sq = Pushout {A = CubeBoundary} {B = 2Sq} {C = Cubic} h k

inl23 : 2Sq → 3Sq
inl23 = inl

inr23 : Cubic → 3Sq
inr23 = inr

push23 : (x : CubeBoundary) → inl23 (h x) ≡ inr23 (k x)
push23 = push

congCube :
  {A : Type ℓ} {B : Type ℓ'}
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  {a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁}
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  {a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁}
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  {a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁}
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  {a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁}
  {a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀}
  {a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁}
  (f : A → B) →
  (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) → (Cube (congSquare f a₀₋₋) (congSquare f a₁₋₋) (congSquare f a₋₀₋) (congSquare f a₋₁₋) (congSquare f a₋₋₀) (congSquare f a₋₋₁))
congCube  = λ f c i j k → f (c i j k)


cubefill' : Cube (congSquare inr23 x₀₋₋) (congSquare inr23 x₁₋₋) (congSquare inr23 x₋₀₋) (congSquare inr23 x₋₁₋) (congSquare inr23 x₋₋₀) (congSquare inr23 x₋₋₁)
cubefill' = congCube inr23 3cell

cubefill : Cube (congSquare inl23 sf1) (congSquare inl23 (rot sf1)) (congSquare inl23 sf3) (congSquare inl23 (anti-rot sf3)) (congSquare inl23 sf5) (congSquare inl23 (rot sf5))
cubefill = {!!} 

sec3 : Hypercubic → 3Sq
sec3 blueV = inl(inl(inr(blueV)))
sec3 whiteV = inl(inl(inl(whiteV)))
sec3 (yellowE i) = cong (inl23 ∘ inl12) (push yellowE) i
sec3 (greenE i) = cong (inl23 ∘ inl12) (push greenE) i
sec3 (redE i) = cong (inl23 ∘ inl12) (push redE) i
sec3 (blueE i) = cong (inl23 ∘ inl12) (push blueE) i
sec3 (f1 i j) = congSquare inl23 sf1 i j
sec3 (f3 i j) = congSquare inl23 sf3 i j
sec3 (f5 i j) = congSquare inl23 sf5 i j
sec3 (3-cell i j k) = cubefill i j k

ret3 : 3Sq → Hypercubic
ret3 (inl (inl (inl whiteV))) = whiteV
ret3 (inl (inl (inr blueV))) = blueV
ret3 (inl (inl (push redE i))) = redE i
ret3 (inl (inl (push blueE i))) = blueE i
ret3 (inl (inl (push greenE i))) = greenE i
ret3 (inl (inl (push yellowE i))) = yellowE i
ret3 (inl (inr (f1 s₀₀))) = blueV
ret3 (inl (inr (f1 s₀₁))) = whiteV
ret3 (inl (inr (f1 s₁₀))) = whiteV
ret3 (inl (inr (f1 s₁₁))) = blueV
ret3 (inl (inr (f1 (s₀₋ i)))) = (sym yellowE) i
ret3 (inl (inr (f1 (s₁₋ i)))) = greenE i
ret3 (inl (inr (f1 (s₋₀ i)))) = (sym blueE) i
ret3 (inl (inr (f1 (s₋₁ i)))) = redE i
ret3 (inl (inr (f1 (2cell i j)))) = f1 i j
ret3 (inl (inr (f3 s₀₀))) = blueV
ret3 (inl (inr (f3 s₀₁))) = whiteV
ret3 (inl (inr (f3 s₁₀))) = whiteV
ret3 (inl (inr (f3 s₁₁))) = blueV
ret3 (inl (inr (f3 (s₀₋ i)))) = (sym yellowE) i
ret3 (inl (inr (f3 (s₁₋ i)))) = blueE i
ret3 (inl (inr (f3 (s₋₀ i)))) = (sym redE) i
ret3 (inl (inr (f3 (s₋₁ i)))) = greenE i
ret3 (inl (inr (f3 (2cell i j)))) = f3 i j
ret3 (inl (inr (f5 s₀₀))) = blueV
ret3 (inl (inr (f5 s₀₁))) = whiteV
ret3 (inl (inr (f5 s₁₀))) = whiteV
ret3 (inl (inr (f5 s₁₁))) = blueV
ret3 (inl (inr (f5 (s₀₋ i)))) = (sym blueE) i
ret3 (inl (inr (f5 (s₁₋ i)))) = greenE i
ret3 (inl (inr (f5 (s₋₀ i)))) = (sym redE) i
ret3 (inl (inr (f5 (s₋₁ i)))) = yellowE i
ret3 (inl (inr (f5 (2cell i j)))) = f5 i j
ret3 (inl (push (i1 c₀₀) i)) = blueV
ret3 (inl (push (i1 c₀₁) i)) = whiteV
ret3 (inl (push (i1 c₁₀) i)) = whiteV
ret3 (inl (push (i1 c₁₁) i)) = blueV
ret3 (inl (push (i1 (c₀₋ i)) j)) = sym yellowE i
ret3 (inl (push (i1 (c₁₋ i)) j)) = greenE i
ret3 (inl (push (i1 (c₋₀ i)) j)) = sym blueE i
ret3 (inl (push (i1 (c₋₁ i)) j)) = redE i
ret3 (inl (push (i2 c₀₀) i)) = blueV
ret3 (inl (push (i2 c₀₁) i)) = whiteV
ret3 (inl (push (i2 c₁₀) i)) = whiteV
ret3 (inl (push (i2 c₁₁) i)) = blueV
ret3 (inl (push (i2 (c₀₋ i)) j)) = sym yellowE i
ret3 (inl (push (i2 (c₁₋ i)) j)) = blueE i
ret3 (inl (push (i2 (c₋₀ i)) j)) = sym redE i
ret3 (inl (push (i2 (c₋₁ i)) j)) = greenE i
ret3 (inl (push (i3 c₀₀) i)) = blueV
ret3 (inl (push (i3 c₀₁) i)) = whiteV
ret3 (inl (push (i3 c₁₀) i)) = whiteV
ret3 (inl (push (i3 c₁₁) i)) = blueV
ret3 (inl (push (i3 (c₀₋ i)) j)) = sym blueE i
ret3 (inl (push (i3 (c₁₋ i)) j)) = greenE i
ret3 (inl (push (i3 (c₋₀ i)) j)) = sym redE i
ret3 (inl (push (i3 (c₋₁ i)) j)) = yellowE i
ret3 (inr x₀₀₀) = blueV
ret3 (inr x₀₀₁) = whiteV
ret3 (inr x₀₁₀) = whiteV
ret3 (inr x₀₁₁) = blueV
ret3 (inr x₁₀₀) = whiteV
ret3 (inr x₁₀₁) = blueV
ret3 (inr x₁₁₀) = blueV
ret3 (inr x₁₁₁) = whiteV
ret3 (inr (x₀₀₋ i)) = sym yellowE i
ret3 (inr (x₀₁₋ i)) = greenE i
ret3 (inr (x₀₋₀ i)) = sym blueE i
ret3 (inr (x₀₋₁ i)) = redE i
ret3 (inr (x₁₀₋ i)) = blueE i
ret3 (inr (x₁₁₋ i)) = sym redE i
ret3 (inr (x₁₋₀ i)) = greenE i
ret3 (inr (x₁₋₁ i)) = sym yellowE i
ret3 (inr (x₋₀₀ i)) = sym redE  i
ret3 (inr (x₋₀₁ i)) = greenE i
ret3 (inr (x₋₁₀ i)) = yellowE i
ret3 (inr (x₋₁₁ i)) = sym blueE i
ret3 (inr (x₀₋₋ i j)) = f1 i j
ret3 (inr (x₁₋₋ i j)) = (rot f1) i j
ret3 (inr (x₋₀₋ i j)) = f3 i j
ret3 (inr (x₋₁₋ i j)) = (anti-rot f3) i j
ret3 (inr (x₋₋₀ i j)) = f5 i j
ret3 (inr (x₋₋₁ i j)) = (rot f5) i j
ret3 (inr (3cell i j k)) = 3-cell i j k
ret3 (push a₀₀₀ i) = blueV
ret3 (push a₀₀₁ i) = whiteV
ret3 (push a₀₁₀ i) = whiteV
ret3 (push a₀₁₁ i) = blueV
ret3 (push a₁₀₀ i) = whiteV
ret3 (push a₁₀₁ i) = blueV
ret3 (push a₁₁₀ i) = blueV
ret3 (push a₁₁₁ i) = whiteV
ret3 (push (a₀₀₋ i) j) = (sym yellowE) i
ret3 (push (a₀₁₋ i) j) = greenE i
ret3 (push (a₀₋₀ i) j) = sym blueE i
ret3 (push (a₀₋₁ i) j) = redE i
ret3 (push (a₁₀₋ i) j) = blueE i
ret3 (push (a₁₁₋ i) j) = sym redE i
ret3 (push (a₁₋₀ i) j) = greenE i
ret3 (push (a₁₋₁ i) j) = (sym yellowE) i
ret3 (push (a₋₀₀ i) j) = sym redE i
ret3 (push (a₋₀₁ i) j) = greenE i
ret3 (push (a₋₁₀ i) j) = yellowE i
ret3 (push (a₋₁₁ i) j) = (sym blueE) i
ret3 (push (a₀₋₋ i j) k) = {!!}
ret3 (push (a₁₋₋ i j) k) = {!!}
ret3 (push (a₋₀₋ i j) k) = {!!}
ret3 (push (a₋₁₋ i j) k) = {!!}
ret3 (push (a₋₋₀ i j) k) = {!!}
ret3 (push (a₋₋₁ i j) k) = {!!}

isIdsec3rec3 : section sec3 ret3 
isIdsec3rec3 (inl (inl (inl whiteV))) = refl
isIdsec3rec3 (inl (inl (inr blueV))) = refl
isIdsec3rec3 (inl (inl (push redE i))) = refl
isIdsec3rec3 (inl (inl (push blueE i))) = refl
isIdsec3rec3 (inl (inl (push greenE i))) = refl
isIdsec3rec3 (inl (inl (push yellowE i))) = refl
isIdsec3rec3 (inl (inr (f1 s₀₀))) = cong inl23 (push (i1 c₀₀))
isIdsec3rec3 (inl (inr (f1 s₀₁))) = cong inl23 (push (i1 c₀₁))
isIdsec3rec3 (inl (inr (f1 s₁₀))) = cong inl23 (push (i1 c₁₀))
isIdsec3rec3 (inl (inr (f1 s₁₁))) = cong inl23 (push (i1 c₁₁))
isIdsec3rec3 (inl (inr (f1 (s₀₋ i)))) = cong inl23(push (i1 (c₀₋ i)))
isIdsec3rec3 (inl (inr (f1 (s₁₋ i)))) = cong inl23(push (i1 (c₁₋ i)))
isIdsec3rec3 (inl (inr (f1 (s₋₀ i)))) = cong inl23(push (i1 (c₋₀ i)))
isIdsec3rec3 (inl (inr (f1 (s₋₁ i)))) = cong inl23(push (i1 (c₋₁ i)))
isIdsec3rec3 (inl (inr (f1 (2cell i j)))) = {!   !}
isIdsec3rec3 (inl (inr (f3 s₀₀))) = cong inl23 (push (i2 c₀₀))
isIdsec3rec3 (inl (inr (f3 s₀₁))) = cong inl23 (push (i2 c₀₁))
isIdsec3rec3 (inl (inr (f3 s₁₀))) = cong inl23 (push (i2 c₁₀))
isIdsec3rec3 (inl (inr (f3 s₁₁))) = cong inl23 (push (i2 c₁₁))
isIdsec3rec3 (inl (inr (f3 (s₀₋ i)))) = cong inl23(push (i2 (c₀₋ i)))
isIdsec3rec3 (inl (inr (f3 (s₁₋ i)))) = cong inl23(push (i2 (c₁₋ i)))
isIdsec3rec3 (inl (inr (f3 (s₋₀ i)))) = cong inl23(push (i2 (c₋₀ i)))
isIdsec3rec3 (inl (inr (f3 (s₋₁ i)))) = cong inl23(push (i2 (c₋₁ i)))
isIdsec3rec3 (inl (inr (f3 (2cell i j)))) = {!   !}
isIdsec3rec3 (inl (inr (f5 s₀₀))) = cong inl23 (push (i3 c₀₀))
isIdsec3rec3 (inl (inr (f5 s₀₁))) = cong inl23 (push (i3 c₀₁))
isIdsec3rec3 (inl (inr (f5 s₁₀))) = cong inl23 (push (i3 c₁₀))
isIdsec3rec3 (inl (inr (f5 s₁₁))) = cong inl23 (push (i3 c₁₁))
isIdsec3rec3 (inl (inr (f5 (s₀₋ i)))) = cong inl23(push (i3 (c₀₋ i)))
isIdsec3rec3 (inl (inr (f5 (s₁₋ i)))) = cong inl23(push (i3 (c₁₋ i)))
isIdsec3rec3 (inl (inr (f5 (s₋₀ i)))) = cong inl23(push (i3 (c₋₀ i)))
isIdsec3rec3 (inl (inr (f5 (s₋₁ i)))) = cong inl23(push (i3 (c₋₁ i)))
isIdsec3rec3 (inl (inr (f5 (2cell i j)))) = {!   !}
isIdsec3rec3 (inl (push (i1 c₀₀) i)) = {!  !}
isIdsec3rec3 (inl (push (i1 c₀₁) i)) = {!   !}
isIdsec3rec3 (inl (push (i1 c₁₀) i)) = {!   !}
isIdsec3rec3 (inl (push (i1 c₁₁) i)) = {!   !}
isIdsec3rec3 (inl (push (i1 (c₀₋ i)) j)) = {!   !}
isIdsec3rec3 (inl (push (i1 (c₁₋ i)) j)) = {!   !}
isIdsec3rec3 (inl (push (i1 (c₋₀ i)) j)) = {!   !}
isIdsec3rec3 (inl (push (i1 (c₋₁ i)) j)) = {!   !}
isIdsec3rec3 (inl (push (i2 x) i)) = {!   !}
isIdsec3rec3 (inl (push (i3 x) i)) = {!   !}
isIdsec3rec3 (inr x₀₀₀) = push a₀₀₀
isIdsec3rec3 (inr x₀₀₁) = push a₀₀₁
isIdsec3rec3 (inr x₀₁₀) = push a₀₁₀
isIdsec3rec3 (inr x₀₁₁) = push a₀₁₁
isIdsec3rec3 (inr x₁₀₀) = push a₁₀₀
isIdsec3rec3 (inr x₁₀₁) = push a₁₀₁
isIdsec3rec3 (inr x₁₁₀) = push a₁₁₀
isIdsec3rec3 (inr x₁₁₁) = push a₁₁₁
isIdsec3rec3 (inr (x₀₀₋ i)) = push (a₀₀₋ i)
isIdsec3rec3 (inr (x₀₁₋ i)) = push (a₀₁₋ i)
isIdsec3rec3 (inr (x₀₋₀ i)) = push (a₀₋₀ i)
isIdsec3rec3 (inr (x₀₋₁ i)) = push (a₀₋₁ i)
isIdsec3rec3 (inr (x₁₀₋ i)) = push (a₁₀₋ i)
isIdsec3rec3 (inr (x₁₁₋ i)) = push (a₁₁₋ i)
isIdsec3rec3 (inr (x₁₋₀ i)) = push (a₁₋₀ i)
isIdsec3rec3 (inr (x₁₋₁ i)) = push (a₁₋₁ i)
isIdsec3rec3 (inr (x₋₀₀ i)) = push (a₋₀₀ i)
isIdsec3rec3 (inr (x₋₀₁ i)) = push (a₋₀₁ i)
isIdsec3rec3 (inr (x₋₁₀ i)) = push (a₋₁₀ i)
isIdsec3rec3 (inr (x₋₁₁ i)) = push (a₋₁₁ i)
isIdsec3rec3 (inr (x₀₋₋ i j)) = push (a₀₋₋ i j)
isIdsec3rec3 (inr (x₁₋₋ i j)) = push (a₁₋₋ i j)
isIdsec3rec3 (inr (x₋₀₋ i j)) = push (a₋₀₋ i j)
isIdsec3rec3 (inr (x₋₁₋ i j)) = push (a₋₁₋ i j)
isIdsec3rec3 (inr (x₋₋₀ i j)) = push (a₋₋₀ i j)
isIdsec3rec3 (inr (x₋₋₁ i j)) = push (a₋₋₁ i j)
isIdsec3rec3 (inr (3cell i j k)) = {!   !}
isIdsec3rec3 (push a₀₀₀ i) = {!!}
isIdsec3rec3 (push a₀₀₁ i) = {!   !}
isIdsec3rec3 (push a₀₁₀ i) = {!   !}
isIdsec3rec3 (push a₀₁₁ i) = {!   !}
isIdsec3rec3 (push a₁₀₀ i) = {!   !}
isIdsec3rec3 (push a₁₀₁ i) = {!   !}
isIdsec3rec3 (push a₁₁₀ i) = {!   !}
isIdsec3rec3 (push a₁₁₁ i) = {!   !}
isIdsec3rec3 (push (a₀₀₋ i) j) = {!   !}
isIdsec3rec3 (push (a₀₁₋ i) j) = {!   !}
isIdsec3rec3 (push (a₀₋₀ i) j) = {!   !}
isIdsec3rec3 (push (a₀₋₁ i) j) = {!   !}
isIdsec3rec3 (push (a₁₀₋ i) j) = {!   !}
isIdsec3rec3 (push (a₁₁₋ i) j) = {!   !}
isIdsec3rec3 (push (a₁₋₀ i) j) = {!   !}
isIdsec3rec3 (push (a₁₋₁ i) j) = {!   !}
isIdsec3rec3 (push (a₋₀₀ i) j) = {!   !}
isIdsec3rec3 (push (a₋₀₁ i) j) = {!   !}
isIdsec3rec3 (push (a₋₁₀ i) j) = {!   !}
isIdsec3rec3 (push (a₋₁₁ i) j) = {!   !}
isIdsec3rec3 (push (a₀₋₋ i j) k) = {!   !}
isIdsec3rec3 (push (a₁₋₋ i j) k) = {!   !}
isIdsec3rec3 (push (a₋₀₋ i j) k) = {!   !}
isIdsec3rec3 (push (a₋₁₋ i j) k) = {!   !}
isIdsec3rec3 (push (a₋₋₀ i j) k) = {!   !}
isIdsec3rec3 (push (a₋₋₁ i j) k) = {!   !}

isIdrec3sec3 : retract sec3 ret3 
isIdrec3sec3 blueV = refl
isIdrec3sec3 whiteV = refl
isIdrec3sec3 (yellowE i) = refl
isIdrec3sec3 (greenE i) = refl
isIdrec3sec3 (redE i) = refl
isIdrec3sec3 (blueE i) = refl
isIdrec3sec3 (f1 i j) = {!   !}
isIdrec3sec3 (f3 i j) = {!   !}
isIdrec3sec3 (f5 i j) = {!   !}
isIdrec3sec3 (3-cell i j k) = {!   !}

3SqOk : Iso 3Sq Hypercubic 
3SqOk = iso ret3 sec3 isIdrec3sec3 isIdsec3rec3