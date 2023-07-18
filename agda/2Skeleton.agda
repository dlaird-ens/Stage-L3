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

-- 1ère tentatative avec des vraies face "Square"

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
ret2 (inr (f1 (2cell i j))) = f1 i j {-dans ce trou on veut mettre f1 i j et ça marche bien, mais il faut remarquer que le type que ça demande correspond aux attendus-}

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
Cependant, agda m'affiche des soucis de contraintes non réglées? -}
ret2 (push (i1 c₀₀) i) = blueV
ret2 (push (i1 c₀₁) i) = whiteV
ret2 (push (i1 c₁₀) i) = whiteV
ret2 (push (i1 c₁₁) i) = blueV
ret2 (push (i1 (c₀₋ i)) j) = sym yellowE i
ret2 (push (i1 (c₁₋ i)) j) = greenE i
ret2 (push (i1 (c₋₀ i)) j) = sym blueE i
ret2 (push (i1 (c₋₁ i)) j) = redE i
ret2 (push (i2 c₀₀) i) = blueV
ret2 (push (i2 c₀₁) i) = whiteV
ret2 (push (i2 c₁₀) i) = whiteV
ret2 (push (i2 c₁₁) i) = blueV
ret2 (push (i2 (c₀₋ i)) j) = sym yellowE i
ret2 (push (i2 (c₁₋ i)) j) = blueE i
ret2 (push (i2 (c₋₀ i)) j) = sym redE i
ret2 (push (i2 (c₋₁ i)) j) = greenE i
ret2 (push (i3 c₀₀) i) = blueV
ret2 (push (i3 c₀₁) i) = whiteV
ret2 (push (i3 c₁₀) i) = whiteV
ret2 (push (i3 c₁₁) i) = blueV
ret2 (push (i3 (c₀₋ i)) j) = sym blueE i
ret2 (push (i3 (c₁₋ i)) j) = greenE i
ret2 (push (i3 (c₋₀ i)) j) = sym redE i
ret2 (push (i3 (c₋₁ i)) j) = yellowE i

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


-- f1 : Square (sym yellowE) greenE (sym blueE) redE
-- Square (inl (push (sym yellowE))) (inl (push greenE)) (inl (push (sym blueE))) (inl (push redE))
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
sf1 i j = {!!}

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

sec2 : Hypercubic2 → 2Sq

{-Correspondance entre les sommets-}
sec2 blueV = inl(inr(blueV))
sec2 whiteV = inl(inl(whiteV))

{-Correspondance entre les arêtes-}
sec2 (yellowE i) = cong inl12 (push yellowE) i
sec2 (greenE i) = cong inl12 (push greenE) i
sec2 (redE i) = cong inl12 (push redE) i
sec2 (blueE i) = cong inl12 (push blueE) i

{-Correspondance entre les remplissements des faces.
Ici, on voudrait mettre des trucs de la forme inr(f1 (2cell i j))).-}

sec2 (f1 i j) = sf1 i j
sec2 (f3 i j) = sf3 i j
sec2 (f5 i j) = sf5 i j


isIdsec2rec2 : section sec2 ret2 
isIdsec2rec2 (inl (inl whiteV)) = refl
isIdsec2rec2 (inl (inr blueV)) = refl
isIdsec2rec2 (inl (push redE i)) = refl
isIdsec2rec2 (inl (push blueE i)) = refl
isIdsec2rec2 (inl (push greenE i)) = refl
isIdsec2rec2 (inl (push yellowE i)) = refl
isIdsec2rec2 (inr (f1 s₀₀)) = push (i1 c₀₀)
isIdsec2rec2 (inr (f1 s₀₁)) = push (i1 c₀₁)
isIdsec2rec2 (inr (f1 s₁₀)) = push (i1 c₁₀)
isIdsec2rec2 (inr (f1 s₁₁)) = push (i1 c₁₁)
isIdsec2rec2 (inr (f1 (s₀₋ i))) = push(i1 (c₀₋ i))
isIdsec2rec2 (inr (f1 (s₁₋ i))) = push(i1 (c₁₋ i))
isIdsec2rec2 (inr (f1 (s₋₀ i))) = push(i1 (c₋₀ i))
isIdsec2rec2 (inr (f1 (s₋₁ i))) = push(i1 (c₋₁ i))
isIdsec2rec2 (inr (f1 (2cell i j))) = {!   !}
isIdsec2rec2 (inr (f3 s₀₀)) = push(i2 c₀₀)
isIdsec2rec2 (inr (f3 s₀₁)) = push(i2 c₀₁)
isIdsec2rec2 (inr (f3 s₁₀)) = push(i2 c₁₀)
isIdsec2rec2 (inr (f3 s₁₁)) = push(i2 c₁₁)
isIdsec2rec2 (inr (f3 (s₀₋ i))) = push(i2 (c₀₋ i))
isIdsec2rec2 (inr (f3 (s₁₋ i))) = push(i2 (c₁₋ i))
isIdsec2rec2 (inr (f3 (s₋₀ i))) = push(i2 (c₋₀ i))
isIdsec2rec2 (inr (f3 (s₋₁ i))) = push(i2 (c₋₁ i))
isIdsec2rec2 (inr (f3 (2cell i j))) = {!   !}
isIdsec2rec2 (inr (f5 s₀₀)) = push(i3 c₀₀)
isIdsec2rec2 (inr (f5 s₀₁)) = push(i3 c₀₁)
isIdsec2rec2 (inr (f5 s₁₀)) = push(i3 c₁₀)
isIdsec2rec2 (inr (f5 s₁₁)) = push(i3 c₁₁)
isIdsec2rec2 (inr (f5 (s₀₋ i))) = push(i3 (c₀₋ i))
isIdsec2rec2 (inr (f5 (s₁₋ i))) = push(i3 (c₁₋ i))
isIdsec2rec2 (inr (f5 (s₋₀ i))) = push(i3 (c₋₀ i))
isIdsec2rec2 (inr (f5 (s₋₁ i))) = push(i3 (c₋₁ i))
isIdsec2rec2 (inr (f5 (2cell i j))) = {!   !}
isIdsec2rec2 (push (i1 c₀₀) i) = {!!}
isIdsec2rec2 (push (i1 c₀₁) i) = {!   !}
isIdsec2rec2 (push (i1 c₁₀) i) = {!   !}
isIdsec2rec2 (push (i1 c₁₁) i) = {!   !}
isIdsec2rec2 (push (i1 (c₀₋ i)) j) = {!   !}
isIdsec2rec2 (push (i1 (c₁₋ i)) j) = {!   !}
isIdsec2rec2 (push (i1 (c₋₀ i)) j) = {!   !}
isIdsec2rec2 (push (i1 (c₋₁ i)) j) = {!   !}
isIdsec2rec2 (push (i2 x) i) = {!   !}
isIdsec2rec2 (push (i3 x) i) = {!   !}


isIdrec2sec2 : retract sec2 ret2 
isIdrec2sec2 blueV = refl
isIdrec2sec2 whiteV = refl
isIdrec2sec2 (yellowE i) = refl
isIdrec2sec2 (greenE i) = refl
isIdrec2sec2 (redE i) = refl
isIdrec2sec2 (blueE i) = refl
isIdrec2sec2 (f1 i j) = {!!}
isIdrec2sec2 (f3 i j) = {!   !}
isIdrec2sec2 (f5 i j) = {!   !}

2SqOk : Iso 2Sq Hypercubic2 
2SqOk = iso ret2 sec2 isIdrec2sec2 isIdsec2rec2















 