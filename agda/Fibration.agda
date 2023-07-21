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
HypercubicToDelooping ∣ redE i ∣₃ = emloop Q-k i 
HypercubicToDelooping ∣ blueE i ∣₃ = emloop Qi i
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

postulate flatten1 : (Σ (Pushout h k) fibration) ≡ Pushout ΣfibrationOver2Sq ΣfibrationOverCubic

-- On refait un flattening lemma cette fois ci pour le 2-squelette

fibrationOver1Sq : 1Sq → Type
fibrationOver1Sq = fibrationOver2Sq ∘ inl12

fibrationOverSides : sides → Type 
fibrationOverSides = fibrationOver2Sq ∘ inr12

GlueFromCircles : (x : (triple Circle Circle Circle)) → (fibrationOver1Sq (f x)) ≃ (fibrationOverSides (g x))
GlueFromCircles x = pathToEquiv (cong fibrationOver2Sq (push x))

fibrationOver2Skeleton : Pushout f g → Type
fibrationOver2Skeleton (inl x) = fibrationOver1Sq x
fibrationOver2Skeleton (inr x) = fibrationOverSides x
fibrationOver2Skeleton (push e i) = ua (GlueFromCircles e) i 

ΣfibrationOver1Sq : Σ[ x ∈ (triple Circle Circle Circle) ] ((fibrationOver1Sq ∘ f) x) → Σ[ x ∈ 1Sq ] (fibrationOver1Sq x)
ΣfibrationOver1Sq (fst , snd) = (f fst) , snd

ΣfibrationOverSides : Σ[ x ∈ (triple Circle Circle Circle) ] ((fibrationOver1Sq ∘ f) x) → Σ[ x ∈ sides ] (fibrationOverSides x)
ΣfibrationOverSides  = λ x → (g (fst x)) , (fst (GlueFromCircles (fst x))) (snd x)

postulate flatten2 : (Σ (Pushout f g) fibrationOver2Sq) ≡ Pushout ΣfibrationOver1Sq ΣfibrationOverSides


-- Et enfin pour le 1-squelette

fibrationOverWhiteVertice : WhiteVertice → Type 
fibrationOverWhiteVertice = fibrationOver1Sq ∘ inl01

fibrationOverBlueVertice : BlueVertice → Type
fibrationOverBlueVertice = fibrationOver1Sq ∘ inr01

fibrationOverEdges : edges → Type
fibrationOverEdges = fibrationOverWhiteVertice ∘ source  

GlueFromEdges : (x : edges) → (fibrationOverWhiteVertice (source x)) ≃ (fibrationOverBlueVertice (target x))
GlueFromEdges x = pathToEquiv (cong fibrationOver1Sq (push x))

fibrationOver1Skeleton : Pushout source target → Type
fibrationOver1Skeleton (inl x) = fibrationOverWhiteVertice x
fibrationOver1Skeleton (inr x) = fibrationOverBlueVertice x
fibrationOver1Skeleton (push e i) = ua (GlueFromEdges e) i 

ΣfibrationOverWhiteVertice : Σ[ x ∈ edges ] ((fibrationOverWhiteVertice ∘ source) x) → Σ[ x ∈ WhiteVertice ] (fibrationOverWhiteVertice x)
ΣfibrationOverWhiteVertice = λ x → (source (fst x)) , (snd x)

ΣfibrationOverBlueVertice : Σ[ x ∈ edges ] ((fibrationOverWhiteVertice ∘ source) x) → Σ[ x ∈ BlueVertice ] (fibrationOverBlueVertice x)
ΣfibrationOverBlueVertice  = λ x → (target (fst x)) , ((fst (GlueFromEdges (fst x))) (snd x))

postulate flatten3 : (Σ (Pushout source target) fibrationOver1Sq) ≡ Pushout ΣfibrationOverWhiteVertice ΣfibrationOverBlueVertice



-- Calcul du premier Pushout

TotSpaceBlueVerticeToBaseLoop : (Σ[ x ∈ BlueVertice ] (fibrationOverBlueVertice x)) → (embase ≡ embase)  
TotSpaceBlueVerticeToBaseLoop (blueV , snd) = snd

BaseLoopToTotSpaceBlueVertice : (embase ≡ embase) → (Σ[ x ∈ BlueVertice ] (fibrationOverBlueVertice x))
BaseLoopToTotSpaceBlueVertice l = blueV , l

sectionTotSpaceBlueVerticeToBaseLoopBaseLoopToTotSpaceBlueVertice  : section TotSpaceBlueVerticeToBaseLoop BaseLoopToTotSpaceBlueVertice
sectionTotSpaceBlueVerticeToBaseLoopBaseLoopToTotSpaceBlueVertice x = refl

retractTotSpaceBlueVerticeToBaseLoopBaseLoopToTotSpaceBlueVertice : retract TotSpaceBlueVerticeToBaseLoop BaseLoopToTotSpaceBlueVertice
retractTotSpaceBlueVerticeToBaseLoopBaseLoopToTotSpaceBlueVertice (blueV , snd) = refl

TotSpaceBlueVertice≡BaseLoop :  (Σ[ x ∈ BlueVertice ] (fibrationOverBlueVertice x)) ≡  (embase ≡ embase)  
TotSpaceBlueVertice≡BaseLoop = isoToPath (iso TotSpaceBlueVerticeToBaseLoop BaseLoopToTotSpaceBlueVertice sectionTotSpaceBlueVerticeToBaseLoopBaseLoopToTotSpaceBlueVertice retractTotSpaceBlueVerticeToBaseLoopBaseLoopToTotSpaceBlueVertice)


TotSpaceWhiteVerticeToBaseLoop : (Σ[ x ∈ WhiteVertice ] (fibrationOverWhiteVertice x)) → (embase ≡ embase)  
TotSpaceWhiteVerticeToBaseLoop (whiteV , snd) = snd

BaseLoopToTotSpaceWhiteVertice : (embase ≡ embase) → (Σ[ x ∈ WhiteVertice ] (fibrationOverWhiteVertice x))
BaseLoopToTotSpaceWhiteVertice l = whiteV , l

sectionTotSpaceWhiteVerticeToBaseLoopBaseLoopToTotSpaceWhiteVertice  : section TotSpaceWhiteVerticeToBaseLoop BaseLoopToTotSpaceWhiteVertice
sectionTotSpaceWhiteVerticeToBaseLoopBaseLoopToTotSpaceWhiteVertice x = refl

retractTotSpaceWhiteVerticeToBaseLoopBaseLoopToTotSpaceWhiteVertice : retract TotSpaceWhiteVerticeToBaseLoop BaseLoopToTotSpaceWhiteVertice
retractTotSpaceWhiteVerticeToBaseLoopBaseLoopToTotSpaceWhiteVertice (whiteV , snd) = refl

TotSpaceWhiteVertice≡BaseLoop :  (Σ[ x ∈ WhiteVertice ] (fibrationOverWhiteVertice x)) ≡  (embase ≡ embase)  
TotSpaceWhiteVertice≡BaseLoop = isoToPath (iso TotSpaceWhiteVerticeToBaseLoop BaseLoopToTotSpaceWhiteVertice sectionTotSpaceWhiteVerticeToBaseLoopBaseLoopToTotSpaceWhiteVertice retractTotSpaceWhiteVerticeToBaseLoopBaseLoopToTotSpaceWhiteVertice)

data quadloop : Type where 
    i1 : embase ≡ embase → quadloop
    i2 : embase ≡ embase → quadloop 
    i3 : embase ≡ embase → quadloop  
    i4 : embase ≡ embase → quadloop 


TotSpaceEdgesToQuadLoop : (Σ[ x ∈ edges ] (fibrationOverEdges x)) → quadloop 
TotSpaceEdgesToQuadLoop (redE , snd) = i1 snd
TotSpaceEdgesToQuadLoop (blueE , snd) = i2 snd
TotSpaceEdgesToQuadLoop (greenE , snd) = i3 snd
TotSpaceEdgesToQuadLoop (yellowE , snd) = i4 snd

QuadLoopToTotSpaceEdges : quadloop → (Σ[ x ∈ edges ] (fibrationOverEdges x))
QuadLoopToTotSpaceEdges (i1 x) = redE , x
QuadLoopToTotSpaceEdges (i2 x) = blueE , x
QuadLoopToTotSpaceEdges (i3 x) = greenE , x
QuadLoopToTotSpaceEdges (i4 x) = yellowE , x

sectionTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges : section TotSpaceEdgesToQuadLoop QuadLoopToTotSpaceEdges
sectionTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (i1 x) = refl
sectionTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (i2 x) = refl
sectionTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (i3 x) = refl
sectionTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (i4 x) = refl

retractTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges : retract TotSpaceEdgesToQuadLoop QuadLoopToTotSpaceEdges
retractTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (redE , snd) = refl
retractTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (blueE , snd) = refl
retractTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (greenE , snd) = refl
retractTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges (yellowE , snd) = refl


TotSpaceEdges≡QuadLoop :  (Σ[ x ∈ edges ] (fibrationOverEdges x)) ≡  quadloop
TotSpaceEdges≡QuadLoop = isoToPath (iso TotSpaceEdgesToQuadLoop QuadLoopToTotSpaceEdges sectionTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges retractTotSpaceEdgesToQuadLoopQuadLoopToTotSpaceEdges)


ResultOfFlattening : Pushout ΣfibrationOverWhiteVertice ΣfibrationOverBlueVertice ≡ Pushout (TotSpaceWhiteVerticeToBaseLoop ∘ ΣfibrationOverWhiteVertice) (TotSpaceBlueVerticeToBaseLoop ∘ ΣfibrationOverBlueVertice)

test : Pushout ΣfibrationOverWhiteVertice ΣfibrationOverBlueVertice → Pushout (TotSpaceWhiteVerticeToBaseLoop ∘ ΣfibrationOverWhiteVertice) (TotSpaceBlueVerticeToBaseLoop ∘ ΣfibrationOverBlueVertice)
test (inl x) = inl (TotSpaceWhiteVerticeToBaseLoop x)
test (inr x) = inr (TotSpaceBlueVerticeToBaseLoop x)
test (push e i) = {!  !}

ResultOfFlattening = isoToPath (iso {!   !} {!   !} {!   !} {!   !}) 

