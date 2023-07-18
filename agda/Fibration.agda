{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import HiTs
open import 1Skeleton
open import 2SkeletonBase
open import 2Skeleton
open import 3Skeleton renaming (3Sq to HypercubicPushout; ret3 to HypercubicPushoutToHypercubic)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv 
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
open import Cubical.HITs.Pushout.Flattening


DeloopingQuaternions = EM₁ QuaternionGroup


HypercubicToDelooping : ∥ Hypercubic ∥₃ → DeloopingQuaternions
HypercubicToDelooping ∣ blueV ∣₃ = embase
HypercubicToDelooping ∣ whiteV ∣₃ = embase
HypercubicToDelooping ∣ yellowE i ∣₃ = emloop Qe i
HypercubicToDelooping ∣ greenE i ∣₃ = emloop Qj i
HypercubicToDelooping ∣ redE i ∣₃ = sym (emloop Qk) i
HypercubicToDelooping ∣ blueE i ∣₃ = sym (emloop Q-i) i
HypercubicToDelooping ∣ f1 i j ∣₃ = {! !}
HypercubicToDelooping ∣ f3 i j ∣₃ = {!   !}
HypercubicToDelooping ∣ f5 i j ∣₃ = {!   !}
HypercubicToDelooping ∣ 3-cell i j k ∣₃ = {!   !}
HypercubicToDelooping (squash₃ x x₁ p q r s i i₁ i₂) = {! !}


Trunc : Hypercubic → ∥ Hypercubic ∥₃
Trunc x = ∣ x ∣₃

HypercubicPushoutToDelooping : HypercubicPushout → DeloopingQuaternions
HypercubicPushoutToDelooping = HypercubicToDelooping ∘ Trunc ∘ HypercubicPushoutToHypercubic  

P : DeloopingQuaternions → Type
P x = (x ≡ embase)

fibration : HypercubicPushout → Type 
fibration = P ∘ HypercubicPushoutToDelooping


-- On va construire le pushout d'espaces totaux donné par le flattening lemma sur le pushout qui définit le 3-squelette

fibrationOver2Sq : 2Sq → Type
fibrationOver2Sq = fibration ∘ inl23

fibrationOverCubic : Cubic → Type
fibrationOverCubic = fibration ∘ inr23

GlueFromCubeBoundary : (x : CubeBoundary) → (fibrationOver2Sq (h x)) ≃ (fibrationOverCubic (k x))
GlueFromCubeBoundary x = pathToEquiv (cong fibration (push x))

fibrationOverHypercubicPushout : Pushout h k → Type
fibrationOverHypercubicPushout (inl x) = fibrationOver2Sq x
fibrationOverHypercubicPushout (inr x) = fibrationOverCubic x
fibrationOverHypercubicPushout (push e i) = ua (GlueFromCubeBoundary e) i

ΣfibrationOver2Sq : Σ[ x ∈ CubeBoundary ] ((fibrationOver2Sq ∘ h) x) → Σ[ x ∈ 2Sq ] (fibrationOver2Sq x)
ΣfibrationOver2Sq u = (h (fst u)) , (snd u)

ΣfibrationOverCubic : Σ[ x ∈ CubeBoundary ] ((fibrationOver2Sq ∘ h) x) → Σ[ x ∈ Cubic ] (fibrationOverCubic x)
ΣfibrationOverCubic u = (k (fst u)) , (GlueFromCubeBoundary (fst u)) .fst (snd u)


-- On refait un flattening lemma cette fois ci pour le 2-squelette

fibrationOver1Sq : 1Sq → Type
fibrationOver1Sq = fibrationOver2Sq ∘ inl12

fibrationOverSides : sides → Type 
fibrationOverSides = fibrationOver2Sq ∘ inr12

GlueFromCircles : (x : (triple Circle Circle Circle)) → (fibrationOver1Sq (f x)) ≃ (fibrationOverSides (g x))
GlueFromCircles x = pathToEquiv (cong fibrationOver2Sq (push x))

ΣfibrationOver1Sq : Σ[ x ∈ (triple Circle Circle Circle) ] ((fibrationOver1Sq ∘ f) x) → Σ[ x ∈ 1Sq ] (fibrationOver1Sq x)
ΣfibrationOver1Sq (fst , snd) = (f fst) , snd

ΣfibrationOverSides : Σ[ x ∈ (triple Circle Circle Circle) ] ((fibrationOver1Sq ∘ f) x) → Σ[ x ∈ sides ] (fibrationOverSides x)
ΣfibrationOverSides (fst , snd) = g fst , {! !}
-- ΣfibrationOverCubic u = (k (fst u)) , (GlueFromCircles (fst u)) .fst (snd u)

-- Et enfin pour le 1-squelette




  