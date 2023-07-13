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

private
  variable
    ℓ ℓ' : Level
    A : Type
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

data Circle : Type where 
{-Version du cercle avec 4 points et 4 chemins les reliant, ici j'ai choisi les conventions qui sont utilisées pour les Square-}
  c₀₀ : Circle
  c₀₁ : Circle
  c₁₀ : Circle
  c₁₁  : Circle 
  c₀₋ : c₀₀ ≡ c₀₁
  c₁₋ : c₁₀ ≡ c₁₁ 
  c₋₀ : c₀₀ ≡ c₁₀
  c₋₁ : c₀₁ ≡ c₁₁

data triple (A : Type) (B : Type) (C : Type): Type where 
{-Réalise l'union disjointe de trois types-}
  i1 : A → triple A B C 
  i2 : B → triple A B C 
  i3 : C → triple A B C 

f : (triple Circle Circle Circle) → 1Sq

{-Correspondance entre nos 3 cercles et le 1-squelette -}

{-Le premier cercle, qui doit correspondre à la face latérale gauche de la variété hypercubique, i.e f1 -}
f (i1 c₀₀) = inr(blueV)
f (i1 c₀₁) = inl(whiteV)
f (i1 c₁₀) = inl(whiteV)
f (i1 c₁₁) = inr(blueV)
f (i1 (c₀₋ i)) = sym (push yellowE) i
f (i1 (c₁₋ i)) = push greenE i
f (i1 (c₋₀ i)) = sym (push blueE) i
f (i1 (c₋₁ i)) = push redE i 


{-Le deuxième cercle, qui doit correspondre à la face du bas de la variété hypercubique, i.e f3 -}
f (i2 c₀₀) = inr(blueV)
f (i2 c₀₁) = inl(whiteV)
f (i2 c₁₀) = inl(whiteV)
f (i2 c₁₁) = inr(blueV)
f (i2 (c₀₋ i)) = sym (push yellowE) i
f (i2 (c₁₋ i)) = push blueE i
f (i2 (c₋₀ i)) = sym (push redE) i
f (i2 (c₋₁ i)) = push greenE i


{-le troisième cercle, qui doit correspondre à la face de devant de la variété hypercubique, i.e f5 -}
f (i3 c₀₀) = inr(blueV)
f (i3 c₀₁) = inl(whiteV)
f (i3 c₁₀) = inl(whiteV)
f (i3 c₁₁) = inr(blueV)
f (i3 (c₀₋ i)) = sym (push blueE) i
f (i3 (c₁₋ i)) = push greenE i
f (i3 (c₋₀ i)) = sym (push redE) i
f (i3 (c₋₁ i)) = push yellowE i
