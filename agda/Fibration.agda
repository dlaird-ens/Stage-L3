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
open import QuaternionGroup

DeloopingQuaternions = EM₁ QuaternionGroup


HypercubicToDelooping : Hypercubic → DeloopingQuaternions
HypercubicToDelooping blueV = embase
HypercubicToDelooping whiteV = embase
HypercubicToDelooping (yellowE x) = embase
HypercubicToDelooping (greenE x) = emloop j x
HypercubicToDelooping (redE x) = sym (emloop k) x
HypercubicToDelooping (blueE x) = sym (emloop -i) x
HypercubicToDelooping (f1 x y) = {!   !}
HypercubicToDelooping (f3 x y) = {!   !}
HypercubicToDelooping (f5 x y) = {!   !}
HypercubicToDelooping (3-cell x y z) = {!   !} 

 