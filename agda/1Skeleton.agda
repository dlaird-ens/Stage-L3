{-# OPTIONS --cubical #-}
open import HiTs
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

{-On commence par le 1Sq, le PushOut est le suivant

                  edges-------target------> blueV
                  |                             |
                  |                             |
                  s                             |
                  o                             |
                  u                             i
                  r                             n
                  c                             r
                  e                             |
                  |                             |  
                  V                             V
                  whiteV--------inl---------->1Sq


-}

data edges : Type where 
  redE : edges
  blueE : edges
  greenE : edges
  yellowE : edges

data Vertice1 : Type where
  whiteV : Vertice1

data Vertice2 : Type where 
  blueV : Vertice2

source : edges → Vertice1
source redE = whiteV
source blueE = whiteV
source greenE = whiteV
source yellowE = whiteV

target : edges →  Vertice2 
target redE = blueV
target blueE = blueV
target greenE = blueV
target yellowE = blueV

1Sq = Pushout {A = edges} {B = Vertice1} {C = Vertice2} source target 

data Hypercubic1 : Type where 
    blueV : Hypercubic1
    whiteV : Hypercubic1
    yellowE : whiteV ≡ blueV 
    greenE : whiteV ≡ blueV 
    redE : whiteV ≡ blueV 
    blueE : whiteV ≡ blueV 

{-On prouve ici que le 1-squelette que l'on vient de définir par PushOut est bien équivalent à celui de la variété hypercubique-}

sec1 : Hypercubic1 → 1Sq
sec1 blueV = inr(blueV)
sec1 whiteV = inl(whiteV)
sec1 (yellowE i) = push yellowE i
sec1 (greenE i) = push greenE i
sec1 (redE i) = push redE i
sec1 (blueE i) = push blueE i

ret1 : 1Sq → Hypercubic1 
ret1 (inl whiteV) = whiteV
ret1 (inr blueV) = blueV
ret1 (push redE i) = redE i
ret1 (push blueE i) = blueE i
ret1 (push greenE i) = greenE i
ret1 (push yellowE i) = yellowE i

isIdsec1rec1 : section sec1 ret1 
isIdsec1rec1 (inl whiteV) = refl
isIdsec1rec1 (inr blueV) = refl
isIdsec1rec1 (push redE i) = refl
isIdsec1rec1 (push blueE i) = refl
isIdsec1rec1 (push greenE i) = refl
isIdsec1rec1 (push yellowE i) = refl

isIdrec1sec1 : retract sec1 ret1 
isIdrec1sec1 blueV = refl
isIdrec1sec1 whiteV = refl
isIdrec1sec1 (yellowE i) = refl
isIdrec1sec1 (greenE i) = refl
isIdrec1sec1 (redE i) = refl
isIdrec1sec1 (blueE i) = refl

1SqOk : Iso 1Sq Hypercubic1 
1SqOk = iso ret1 sec1 isIdrec1sec1 isIdsec1rec1