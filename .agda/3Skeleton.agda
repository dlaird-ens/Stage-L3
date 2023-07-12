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

data 3cell : Type where
  cell : 3cell

{-On construit encore le 3-squelette par un pushout homotopique
Le pushout est le suivant:

                CubeBoundary -----k---------> 3cell
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


k : CubeBoundary → 3cell
k x = {!!}  