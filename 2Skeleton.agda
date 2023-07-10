{-# OPTIONS --cubical #-}
open import HiTs
open import 1Skeleton
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

data triple (A : Type) (B : Type) (C : Type): Type where 
{-Réalise l'union disjointe de trois types-}
  i1 : A → triple A B C 
  i2 : B → triple A B C 
  i3 : C → triple A B C 


data sides : Type where 
{-On a 3 faces donc on se donne une union disjointe de trois faces. Le nom des injections canoniques correspond à celui des faces de la variété-}
  f1 : side → sides 
  f3 : side → sides 
  f5 : side → sides 

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


ret2 : 2Sq → Hypercubic2 


{-Correspondance entre les sommets-}
ret2 (inl (inl whiteV)) = whiteV
ret2 (inl (inr blueV)) = blueV

{-Correspondance entre les arêtes, bleu et rouge sont inversées à cause des conventions bleu->blanc / blanc->bleu -}
ret2 (inl (push redE i)) = redE i
ret2 (inl (push blueE i)) = blueE i
ret2 (inl (push greenE i)) = greenE i
ret2 (inl (push yellowE i)) = yellowE i

{-Correspondance entre les sommets/arêtes de la 1ère face i.e f1 -}
ret2 (inr (f1 s₀₀)) = blueV
ret2 (inr (f1 s₀₁)) = whiteV
ret2 (inr (f1 s₁₀)) = whiteV
ret2 (inr (f1 s₁₁)) = blueV
ret2 (inr (f1 (s₀₋ i))) = (sym yellowE) i
ret2 (inr (f1 (s₁₋ i))) = greenE i
ret2 (inr (f1 (s₋₀ i))) = (sym blueE) i
ret2 (inr (f1 (s₋₁ i))) = redE i
ret2 (inr (f1 (2cell i j))) = f1 i j{-dans ce trou on veut mettre f1 i j et ça marche bien, mais il faut remarquer que le type que ça demande correspond aux attendus-}

{-Correspondance entre les sommets/arêtes de la 2ème face i.e f3-}

ret2 (inr (f3 s₀₀)) = blueV
ret2 (inr (f3 s₀₁)) = whiteV
ret2 (inr (f3 s₁₀)) = whiteV
ret2 (inr (f3 s₁₁)) = blueV
ret2 (inr (f3 (s₀₋ i))) = (sym yellowE) i
ret2 (inr (f3 (s₁₋ i))) = blueE i
ret2 (inr (f3 (s₋₀ i))) = (sym redE) i
ret2 (inr (f3 (s₋₁ i))) = greenE i
ret2 (inr (f3 (2cell i j))) = f3 i j

{-Correspondance entre les sommets/arêtes de la 3ème face i.e f5 -}
ret2 (inr (f5 s₀₀)) = blueV
ret2 (inr (f5 s₀₁)) = whiteV
ret2 (inr (f5 s₁₀)) = whiteV
ret2 (inr (f5 s₁₁)) = blueV
ret2 (inr (f5 (s₀₋ i))) = (sym blueE) i
ret2 (inr (f5 (s₁₋ i))) = greenE i
ret2 (inr (f5 (s₋₀ i))) = (sym redE) i
ret2 (inr (f5 (s₋₁ i))) = yellowE i
ret2 (inr (f5 (2cell i j))) = f5 i j

{-Ici il faut fournir les chemins qui prouve que la définition de ret2 est cohérente.
Normalement, on a que des égalités définitionnelles (donc des refl) car on a défini cette map pour qu'elle marche bien.
Cependant, agda m'affiche des soucis de contraintes non réglés? -}
ret2 (push (i1 c₀₀) i) = refl i
ret2 (push (i1 c₀₁) i) = refl i
ret2 (push (i1 c₁₀) i) = refl i
ret2 (push (i1 c₁₁) i) = refl i
ret2 (push (i1 (c₀₋ i)) j) = refl i j
ret2 (push (i1 (c₁₋ i)) j) = (refl i) j
ret2 (push (i1 (c₋₀ i)) j) = (refl i) j
ret2 (push (i1 (c₋₁ i)) j) = (refl i) j
ret2 (push (i2 c₀₀) i) = refl i
ret2 (push (i2 c₀₁) i) = refl i
ret2 (push (i2 c₁₀) i) = refl i
ret2 (push (i2 c₁₁) i) = refl i
ret2 (push (i2 (c₀₋ i)) j) = (refl i) j
ret2 (push (i2 (c₁₋ i)) j) = (refl i) j
ret2 (push (i2 (c₋₀ i)) j) = (refl i) j
ret2 (push (i2 (c₋₁ i)) j) = (refl i) j
ret2 (push (i3 c₀₀) i) = refl i
ret2 (push (i3 c₀₁) i) = refl i
ret2 (push (i3 c₁₀) i) = refl i
ret2 (push (i3 c₁₁) i) = refl i
ret2 (push (i3 (c₀₋ i)) j) = (refl i) j
ret2 (push (i3 (c₁₋ i)) j) = (refl i) j
ret2 (push (i3 (c₋₀ i)) j) = (refl i) j
ret2 (push (i3 (c₋₁ i)) j) = (refl i) j 


CorrespondingSquares :  
  {a₀₀ a₀₁ : A} 
  {a₁₀ a₁₁ : A} 
  {b₀₀ b₀₁ : A}
  {b₁₀ b₁₁ : A}
  → (a₀₋ : a₀₀ ≡ a₀₁) 
  → (a₁₋ : a₁₀ ≡ a₁₁)
  → (a₋₀ : a₀₀ ≡ a₁₀) 
  → (a₋₁ : a₀₁ ≡ a₁₁)
  → (b₀₋ : b₀₀ ≡ b₀₁)
  → (b₁₋ : b₁₀ ≡ b₁₁)
  → (b₋₀ : b₀₀ ≡ b₁₀) 
  → (b₋₁ : b₀₁ ≡ b₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁ 
  → Square b₀₋ b₁₋ b₋₀ b₋₁

CorrespondingSquares a₀₋ a₁₋ a₋₀ a₋₁ b₀₋ b₁₋ b₋₀ b₋₁ squareA = {!!}

sec2 : Hypercubic2 → 2Sq

{-Correspondance entre les sommets-}
sec2 blueV = inl(inr(blueV))
sec2 whiteV = inl(inl(whiteV))

{-Correspondanc entre les arêtes-}
sec2 (yellowE i) = inl(push yellowE i)
sec2 (greenE i) = inl(push greenE i)
sec2 (redE i) = inl (push redE i)
sec2 (blueE i) = inl(push blueE i)

{-Correspondance entre les remplissements des faces.
Ici, on voudrait mettre des trucs de la forme inr(f1 (2cell i j))).
Cependant, en regardant ce que demande les trous on voit que systématiquement 
les sens des Red/Blue demandés sont inversés par rapport à ce qui est donné dans la déf de Hypercubic2?
Ca c'est le soucis qui fait que ça passe pas encore, mais j'ai l'impression que c'est surmontable-}
sec2 (f1 i j) = {!!}
sec2 (f3 i j) = {!   !}
sec2 (f5 i j) = {!   !}
