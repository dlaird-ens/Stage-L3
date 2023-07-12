{-# OPTIONS --cubical #-}
open import HiTs
open import 1Skeleton
open import 2Skeleton
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
h (a₀₋₋ i j) = {!!}
h (a₁₋₋ i j) = {!!}
h (a₋₀₋ i j) = {!   !}
h (a₋₁₋ i j) = {!   !}
h (a₋₋₀ i j) = {!   !}
h (a₋₋₁ i j) = {!   !} 