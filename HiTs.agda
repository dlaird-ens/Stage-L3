{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path

private
  variable
    ℓ ℓ' : Level
    A : Type
    x y z : A
    a₀₀ a₀₁ a₁₀ a₁₁ : A
{- Des exemples de HiTs qui ont servi ensuite à la définition de la variété hypercubique-}

-- le Tore à une dimension, aka le Cercle
data Torus1 : Type where
    base : Torus1
    loop : base ≡ base
-- Le Tore T2, aka un produit de cercles
data Torus2 : Type₀ where
  point : Torus2
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2


-- Le ruban de Mobius, un premier exemple de recollement avec des flips d'arêtes
data Mobius : Type where
    a : Mobius
    b : Mobius
    e1 : a ≡ b
    e2 : b ≡ a
    e3 : a ≡ b 
    square : Square e3 (sym e3) e1 e2 
 
-- Le Tore à 3 dimensions, un premier exemple de remplissage de cube
data Torus3 : Type where
    point' : Torus3
    a : point' ≡ point'
    b : point' ≡ point'
    c : point' ≡ point'
    s1 : Square b b a a 
    
    s2 : Square c c a a 
    s3 : Square b b c c  
    cube : Cube s3 s3 s1 s1 s2 s2
-- La suspension par automorphisme du Tore, un premier exemple de recollement par rotation d'une face
data TorusSuspension : Type where
    point : TorusSuspension
    redE' : point ≡ point
    greenE' : point ≡ point
    blueE' : point ≡ point
    f1' : Square blueE' blueE' greenE' redE'
    f2' : Square blueE' blueE' redE' greenE' 
    f3' : Square greenE' greenE' redE' redE'
    3-cell' : Cube f2' f2' f1' f1' (flipSquare f3') f3'

{-La variété hypercubique-}

-- On définit d'abord une rotation d'un quart de tour pour des faces quelconques
rot : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
            {s : a₀₁ ≡ a₁₁} {r : a₀₀ ≡ a₁₀} {p : a₀₀ ≡ a₀₁} {q : a₁₀ ≡ a₁₁} →
            Square p q r s →
            Square (sym r) (sym s) q p
rot sq i j = sq (~ j) i

-- Puis la rotation inverse
anti-rot : {a₀₀ a₀₁ a₁₀ a₁₁ : A} {s : a₀₁ ≡ a₁₁} {r : a₀₀ ≡ a₁₀} {p : a₀₀ ≡ a₀₁} {q : a₁₀ ≡ a₁₁} → Square p q r s → Square s r (sym p) (sym q)
anti-rot sq = rot (rot (rot sq))


-- Et voilà le HiT qui décrit la variété hypercubique comme attendu

data Hypercubic : Type where 
    blueV : Hypercubic
    whiteV : Hypercubic
    yellowE : whiteV ≡ blueV 
    greenE : whiteV ≡ blueV 
    redE : whiteV ≡ blueV
    blueE : whiteV ≡ blueV
    f1 : Square (sym yellowE) greenE (sym blueE) redE
    f3 : Square (sym yellowE) blueE (sym redE) greenE
    f5 : Square (sym blueE) greenE (sym redE) yellowE
    3-cell :
      Cube
      {a₀₀₋ = sym yellowE}
      {a₀₁₋ = greenE}
      {a₀₋₀ = (sym blueE)}
      {a₀₋₁ = redE}
      f1
      {a₁₀₋ = blueE}
      {a₁₁₋ = (sym redE)}
      {a₁₋₀ = greenE}
      {a₁₋₁ = sym yellowE}
      (rot f1)
      {a₋₀₀ = (sym redE)}
      {a₋₀₁ = greenE}
      f3
      (anti-rot f3)
      f5
      (rot f5)