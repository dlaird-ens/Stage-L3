{-# OPTIONS --cubical #-}

open import HiTs
open import 1Skeleton
open import 2SkeletonBase
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.HITs.Pushout 



open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import QuaternionGroup renaming (e to Qe; i to Qi; j to Qj; k to Qk; -e to Q-e; -i to Q-i; -j to Q-j; -k to Q-k)
open import Cubical.HITs.GroupoidTruncation.Base


private
  variable
    ℓ ℓ' : Level
    A : Type
    x y z : A
    a₀₀ a₀₁ a₁₀ a₁₁ : A
    b₀₀ b₀₁ b₁₀ b₁₁ : A 
data side : Type where 
{-Le type d'une face à savoir 4 sommets, 4 arêtes et une preuve que c'est une face, même convention que pour les Square-}
  s₀₀ : side
  s₀₁ : side
  s₁₀ : side
  s₁₁  : side 
  s₀₋ : s₀₀ ≡ s₀₁
  s₁₋ : s₁₀ ≡ s₁₁ 
  s₋₀ : s₀₀ ≡ s₁₀
  s₋₁ : s₀₁ ≡ s₁₁
  2cell : Square s₀₋ s₁₋ s₋₀ s₋₁

data sides : Type where 
  f1 : side → sides 
  f3 : side → sides 
  f5 : side → sides

g : (triple Circle Circle Circle) → sides 

{-La première face, qui doit correspondre à la face latérale gauche de la variété hypercubique, i.e f1 -}
g (i1 c₀₀) = f1 s₀₀
g (i1 c₀₁) = f1 s₀₁
g (i1 c₁₀) = f1 s₁₀
g (i1 c₁₁) = f1 s₁₁
g (i1 (c₀₋ i)) = f1 (s₀₋ i)
g (i1 (c₁₋ i)) = f1 (s₁₋ i)
g (i1 (c₋₀ i)) = f1 (s₋₀ i)
g (i1 (c₋₁ i)) = f1 (s₋₁ i)


{-La deuxième face qui doit correspondre à la face du bas de la variété hypercubique, i.e f3 -}
g (i2 c₀₀) = f3 s₀₀
g (i2 c₀₁) = f3 s₀₁
g (i2 c₁₀) = f3 s₁₀
g (i2 c₁₁) = f3 s₁₁
g (i2 (c₀₋ i)) = f3 (s₀₋ i)
g (i2 (c₁₋ i)) = f3 (s₁₋ i)
g (i2 (c₋₀ i)) = f3 (s₋₀ i)
g (i2 (c₋₁ i)) = f3 (s₋₁ i)


{-La troisième face, qui doit correspondre à la face de devant de la variété hypercubique, i.e f5 -}
g (i3 c₀₀) = f5 s₀₀
g (i3 c₀₁) = f5 s₀₁
g (i3 c₁₀) = f5 s₁₀
g (i3 c₁₁) = f5 s₁₁
g (i3 (c₀₋ i)) = f5 (s₀₋ i)
g (i3 (c₁₋ i)) = f5 (s₁₋ i)
g (i3 (c₋₀ i)) = f5 (s₋₀ i)
g (i3 (c₋₁ i)) = f5 (s₋₁ i)

2Sq = Pushout {A = (triple Circle Circle Circle)} {B = 1Sq} {C = sides} f g

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

inl12 : 1Sq → 2Sq
inl12 = inl

inr12 : sides → 2Sq
inr12 = inr

push12 : (x : triple Circle Circle Circle) → inl12 (f x) ≡ inr12 (g x)
push12 = push

congSquare :
  {A : Type ℓ} {B : Type ℓ'}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  (f : A → B) →
  Square a₀₋ a₁₋ a₋₀ a₋₁ → Square (cong f a₀₋) (cong f a₁₋) (cong f a₋₀) (cong f a₋₁)
congSquare f s i j = f (s i j)

sf1' : Square (cong (inr12 ∘ f1) s₀₋) (cong (inr12 ∘ f1) s₁₋) (cong (inr12 ∘ f1) s₋₀) (cong (inr12 ∘ f1) s₋₁)
sf1' = congSquare (inr12 ∘ f1) 2cell

sf3' : Square (cong (inr12 ∘ f3) s₀₋) (cong (inr12 ∘ f3) s₁₋) (cong (inr12 ∘ f3) s₋₀) (cong (inr12 ∘ f3) s₋₁)
sf3' = congSquare (inr12 ∘ f3) 2cell

sf5' : Square (cong (inr12 ∘ f5) s₀₋) (cong (inr12 ∘ f5) s₁₋) (cong (inr12 ∘ f5) s₋₀) (cong (inr12 ∘ f5) s₋₁)
sf5' = congSquare (inr12 ∘ f5) 2cell

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

sf1 i j = {!!} -- sf1' i j

sf3 : Square
        {A = 2Sq}
        {inl (inr blueV)}
        {inl (inl whiteV)}
        (cong inl12 (sym (push yellowE)))
        {inl (inl whiteV)}
        {inl (inr blueV)}
        (cong inl12 (push blueE))
        (cong inl12 (sym (push redE)))
        (cong inl12 (push greenE))

sf3 i j = {!!} -- sf3' i j

sf5 : Square
        {A = 2Sq}
        {inl (inr blueV)}
        {inl (inl whiteV)}
        (cong inl12 (sym (push blueE)))
        {inl (inl whiteV)}
        {inl (inr blueV)}
        (cong inl12 (push greenE))
        (cong inl12 (sym (push redE)))
        (cong inl12 (push yellowE))

sf5 i j = {!!} -- sf5' i j

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

HypercubicPushout = Pushout {A = CubeBoundary} {B = 2Sq} {C = Cubic} h k

HypercubicPushoutToHypercubic : HypercubicPushout → Hypercubic
HypercubicPushoutToHypercubic (inl (inl (inl whiteV))) = whiteV
HypercubicPushoutToHypercubic (inl (inl (inr blueV))) = blueV
HypercubicPushoutToHypercubic (inl (inl (push redE i))) = redE i
HypercubicPushoutToHypercubic (inl (inl (push blueE i))) = blueE i
HypercubicPushoutToHypercubic (inl (inl (push greenE i))) = greenE i
HypercubicPushoutToHypercubic (inl (inl (push yellowE i))) = yellowE i
HypercubicPushoutToHypercubic (inl (inr (f1 s₀₀))) = blueV
HypercubicPushoutToHypercubic (inl (inr (f1 s₀₁))) = whiteV
HypercubicPushoutToHypercubic (inl (inr (f1 s₁₀))) = whiteV
HypercubicPushoutToHypercubic (inl (inr (f1 s₁₁))) = blueV
HypercubicPushoutToHypercubic (inl (inr (f1 (s₀₋ i)))) = (sym yellowE) i
HypercubicPushoutToHypercubic (inl (inr (f1 (s₁₋ i)))) = greenE i
HypercubicPushoutToHypercubic (inl (inr (f1 (s₋₀ i)))) = (sym blueE) i
HypercubicPushoutToHypercubic (inl (inr (f1 (s₋₁ i)))) = redE i
HypercubicPushoutToHypercubic (inl (inr (f1 (2cell i j)))) = f1 i j
HypercubicPushoutToHypercubic (inl (inr (f3 s₀₀))) = blueV
HypercubicPushoutToHypercubic (inl (inr (f3 s₀₁))) = whiteV
HypercubicPushoutToHypercubic (inl (inr (f3 s₁₀))) = whiteV
HypercubicPushoutToHypercubic (inl (inr (f3 s₁₁))) = blueV
HypercubicPushoutToHypercubic (inl (inr (f3 (s₀₋ i)))) = (sym yellowE) i
HypercubicPushoutToHypercubic (inl (inr (f3 (s₁₋ i)))) = blueE i
HypercubicPushoutToHypercubic (inl (inr (f3 (s₋₀ i)))) = (sym redE) i
HypercubicPushoutToHypercubic (inl (inr (f3 (s₋₁ i)))) = greenE i
HypercubicPushoutToHypercubic (inl (inr (f3 (2cell i j)))) = f3 i j
HypercubicPushoutToHypercubic (inl (inr (f5 s₀₀))) = blueV
HypercubicPushoutToHypercubic (inl (inr (f5 s₀₁))) = whiteV
HypercubicPushoutToHypercubic (inl (inr (f5 s₁₀))) = whiteV
HypercubicPushoutToHypercubic (inl (inr (f5 s₁₁))) = blueV
HypercubicPushoutToHypercubic (inl (inr (f5 (s₀₋ i)))) = (sym blueE) i
HypercubicPushoutToHypercubic (inl (inr (f5 (s₁₋ i)))) = greenE i
HypercubicPushoutToHypercubic (inl (inr (f5 (s₋₀ i)))) = (sym redE) i
HypercubicPushoutToHypercubic (inl (inr (f5 (s₋₁ i)))) = yellowE i
HypercubicPushoutToHypercubic (inl (inr (f5 (2cell i j)))) = f5 i j
HypercubicPushoutToHypercubic (inl (push (i1 c₀₀) i)) = blueV
HypercubicPushoutToHypercubic (inl (push (i1 c₀₁) i)) = whiteV
HypercubicPushoutToHypercubic (inl (push (i1 c₁₀) i)) = whiteV
HypercubicPushoutToHypercubic (inl (push (i1 c₁₁) i)) = blueV
HypercubicPushoutToHypercubic (inl (push (i1 (c₀₋ i)) j)) = sym yellowE i
HypercubicPushoutToHypercubic (inl (push (i1 (c₁₋ i)) j)) = greenE i
HypercubicPushoutToHypercubic (inl (push (i1 (c₋₀ i)) j)) = sym blueE i
HypercubicPushoutToHypercubic (inl (push (i1 (c₋₁ i)) j)) = redE i
HypercubicPushoutToHypercubic (inl (push (i2 c₀₀) i)) = blueV
HypercubicPushoutToHypercubic (inl (push (i2 c₀₁) i)) = whiteV
HypercubicPushoutToHypercubic (inl (push (i2 c₁₀) i)) = whiteV
HypercubicPushoutToHypercubic (inl (push (i2 c₁₁) i)) = blueV
HypercubicPushoutToHypercubic (inl (push (i2 (c₀₋ i)) j)) = sym yellowE i
HypercubicPushoutToHypercubic (inl (push (i2 (c₁₋ i)) j)) = blueE i
HypercubicPushoutToHypercubic (inl (push (i2 (c₋₀ i)) j)) = sym redE i
HypercubicPushoutToHypercubic (inl (push (i2 (c₋₁ i)) j)) = greenE i
HypercubicPushoutToHypercubic (inl (push (i3 c₀₀) i)) = blueV
HypercubicPushoutToHypercubic (inl (push (i3 c₀₁) i)) = whiteV
HypercubicPushoutToHypercubic (inl (push (i3 c₁₀) i)) = whiteV
HypercubicPushoutToHypercubic (inl (push (i3 c₁₁) i)) = blueV
HypercubicPushoutToHypercubic (inl (push (i3 (c₀₋ i)) j)) = sym blueE i
HypercubicPushoutToHypercubic (inl (push (i3 (c₁₋ i)) j)) = greenE i
HypercubicPushoutToHypercubic (inl (push (i3 (c₋₀ i)) j)) = sym redE i
HypercubicPushoutToHypercubic (inl (push (i3 (c₋₁ i)) j)) = yellowE i
HypercubicPushoutToHypercubic (inr x₀₀₀) = blueV
HypercubicPushoutToHypercubic (inr x₀₀₁) = whiteV
HypercubicPushoutToHypercubic (inr x₀₁₀) = whiteV
HypercubicPushoutToHypercubic (inr x₀₁₁) = blueV
HypercubicPushoutToHypercubic (inr x₁₀₀) = whiteV
HypercubicPushoutToHypercubic (inr x₁₀₁) = blueV
HypercubicPushoutToHypercubic (inr x₁₁₀) = blueV
HypercubicPushoutToHypercubic (inr x₁₁₁) = whiteV
HypercubicPushoutToHypercubic (inr (x₀₀₋ i)) = sym yellowE i
HypercubicPushoutToHypercubic (inr (x₀₁₋ i)) = greenE i
HypercubicPushoutToHypercubic (inr (x₀₋₀ i)) = sym blueE i
HypercubicPushoutToHypercubic (inr (x₀₋₁ i)) = redE i
HypercubicPushoutToHypercubic (inr (x₁₀₋ i)) = blueE i
HypercubicPushoutToHypercubic (inr (x₁₁₋ i)) = sym redE i
HypercubicPushoutToHypercubic (inr (x₁₋₀ i)) = greenE i
HypercubicPushoutToHypercubic (inr (x₁₋₁ i)) = sym yellowE i
HypercubicPushoutToHypercubic (inr (x₋₀₀ i)) = sym redE  i
HypercubicPushoutToHypercubic (inr (x₋₀₁ i)) = greenE i
HypercubicPushoutToHypercubic (inr (x₋₁₀ i)) = yellowE i
HypercubicPushoutToHypercubic (inr (x₋₁₁ i)) = sym blueE i
HypercubicPushoutToHypercubic (inr (x₀₋₋ i j)) = f1 i j
HypercubicPushoutToHypercubic (inr (x₁₋₋ i j)) = (rot f1) i j
HypercubicPushoutToHypercubic (inr (x₋₀₋ i j)) = f3 i j
HypercubicPushoutToHypercubic (inr (x₋₁₋ i j)) = (anti-rot f3) i j
HypercubicPushoutToHypercubic (inr (x₋₋₀ i j)) = f5 i j
HypercubicPushoutToHypercubic (inr (x₋₋₁ i j)) = (rot f5) i j
HypercubicPushoutToHypercubic (inr (3cell i j k)) = 3-cell i j k
HypercubicPushoutToHypercubic (push a₀₀₀ i) = blueV
HypercubicPushoutToHypercubic (push a₀₀₁ i) = whiteV
HypercubicPushoutToHypercubic (push a₀₁₀ i) = whiteV
HypercubicPushoutToHypercubic (push a₀₁₁ i) = blueV
HypercubicPushoutToHypercubic (push a₁₀₀ i) = whiteV
HypercubicPushoutToHypercubic (push a₁₀₁ i) = blueV
HypercubicPushoutToHypercubic (push a₁₁₀ i) = blueV
HypercubicPushoutToHypercubic (push a₁₁₁ i) = whiteV
HypercubicPushoutToHypercubic (push (a₀₀₋ i) j) = (sym yellowE) i
HypercubicPushoutToHypercubic (push (a₀₁₋ i) j) = greenE i
HypercubicPushoutToHypercubic (push (a₀₋₀ i) j) = sym blueE i
HypercubicPushoutToHypercubic (push (a₀₋₁ i) j) = redE i
HypercubicPushoutToHypercubic (push (a₁₀₋ i) j) = blueE i
HypercubicPushoutToHypercubic (push (a₁₁₋ i) j) = sym redE i
HypercubicPushoutToHypercubic (push (a₁₋₀ i) j) = greenE i
HypercubicPushoutToHypercubic (push (a₁₋₁ i) j) = (sym yellowE) i
HypercubicPushoutToHypercubic (push (a₋₀₀ i) j) = sym redE i
HypercubicPushoutToHypercubic (push (a₋₀₁ i) j) = greenE i
HypercubicPushoutToHypercubic (push (a₋₁₀ i) j) = yellowE i
HypercubicPushoutToHypercubic (push (a₋₁₁ i) j) = (sym blueE) i
HypercubicPushoutToHypercubic (push (a₀₋₋ i j) k) = f1 i j
HypercubicPushoutToHypercubic (push (a₁₋₋ i j) k) = (rot f1) i j
HypercubicPushoutToHypercubic (push (a₋₀₋ i j) k) = f3 i j
HypercubicPushoutToHypercubic (push (a₋₁₋ i j) k) = (anti-rot f3) i j
HypercubicPushoutToHypercubic (push (a₋₋₀ i j) k) = f5 i j
HypercubicPushoutToHypercubic (push (a₋₋₁ i j) k) = (rot f5) i j


DeloopingQuaternions = EM₁ QuaternionGroup


HypercubicToDelooping : ∥ Hypercubic ∥₃ → DeloopingQuaternions
HypercubicToDelooping ∣ blueV ∣₃ = embase
HypercubicToDelooping ∣ whiteV ∣₃ = embase
HypercubicToDelooping ∣ yellowE i ∣₃ = embase
HypercubicToDelooping ∣ greenE i ∣₃ = emloop Qj i
HypercubicToDelooping ∣ redE i ∣₃ = sym (emloop Qk) i
HypercubicToDelooping ∣ blueE i ∣₃ = sym (emloop Q-i) i
HypercubicToDelooping ∣ f1 i j ∣₃ = {!   !}
HypercubicToDelooping ∣ f3 i j ∣₃ = {!   !}
HypercubicToDelooping ∣ f5 i j ∣₃ = {!   !}
HypercubicToDelooping ∣ 3-cell i j k ∣₃ = {!   !}
HypercubicToDelooping (squash₃ x x₁ p q r s i i₁ i₂) = {!   !}


Trunc : Hypercubic → ∥ Hypercubic ∥₃
Trunc x = ∣ x ∣₃

HypercubicPushoutToDelooping : HypercubicPushout → DeloopingQuaternions
HypercubicPushoutToDelooping = HypercubicToDelooping ∘ Trunc ∘ HypercubicPushoutToHypercubic  
