{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Subgroups.Definition
open import Rings.Cosets
open import Groups.Lemmas
open import Setoids.Functions.Lemmas
open import Rings.Ideals.Definition


module Rings.Ideals.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Divisible.Definition R

idealPredForKernel : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → A → Set d
idealPredForKernel {T = T} R2 {f} fHom a = Setoid._∼_ T (f a) (Ring.0R R2)

idealPredForKernelWellDefined : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → {x y : A} → (Setoid._∼_ S x y) → (idealPredForKernel R2 fHom x → idealPredForKernel R2 fHom y)
idealPredForKernelWellDefined {T = T} R2 {f} fHom a x=0 = Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined (RingHom.groupHom fHom) (Equivalence.symmetric (Setoid.eq S) a)) x=0

kernelIdealIsIdeal : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} {R2 : Ring T _+2_ _*2_} {f : A → C} (fHom : RingHom R R2 f) → Ideal R (idealPredForKernel R2 fHom)
Subgroup.isSubset (Ideal.isSubgroup (kernelIdealIsIdeal {R2 = R2} fHom)) = idealPredForKernelWellDefined R2 fHom
Subgroup.closedUnderPlus (Ideal.isSubgroup (kernelIdealIsIdeal {T = T} {R2 = R2} fHom)) {x} {y} fx=0 fy=0 = transitive (transitive (GroupHom.groupHom (RingHom.groupHom fHom)) (+WellDefined fx=0 fy=0)) identLeft
  where
    open Ring R2
    open Group (Ring.additiveGroup R2)
    open Setoid T
    open Equivalence eq
Subgroup.containsIdentity (Ideal.isSubgroup (kernelIdealIsIdeal fHom)) = imageOfIdentityIsIdentity (RingHom.groupHom fHom)
Subgroup.closedUnderInverse (Ideal.isSubgroup (kernelIdealIsIdeal {T = T} {R2 = R2} fHom)) {x} fx=0 = zeroImpliesInverseZero (RingHom.groupHom fHom) fx=0
  where
    open Ring R2
    open Group (Ring.additiveGroup R2)
    open Setoid T
    open Equivalence eq
Ideal.accumulatesTimes (kernelIdealIsIdeal {T = T} {R2 = R2} {f = f} fHom) {x} {y} fx=0 = transitive (RingHom.ringHom fHom) (transitive (Ring.*WellDefined R2 fx=0 reflexive) (transitive (Ring.*Commutative R2) (Ring.timesZero R2 {f y})))
  where
    open Setoid T
    open Equivalence eq

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq

translate : {c : _} {pred : A → Set c} → (i : Ideal R pred) → {a : A} → pred a → pred (inverse (Ring.0R (cosetRing R i)) + a)
translate {a} i predA = Ideal.isSubset i (transitive (symmetric identLeft) (+WellDefined (symmetric (invIdent additiveGroup)) reflexive)) predA
translate' : {c : _} {pred : A → Set c} → (i : Ideal R pred) → {a : A} → pred (inverse (Ring.0R (cosetRing R i)) + a) → pred a
translate' i = Ideal.isSubset i (transitive (+WellDefined (invIdent additiveGroup) reflexive) identLeft)

inverseImageIsIdeal : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} {R2 : Ring T _+2_ _*2_} {f : C → A} (fHom : RingHom R2 R f) → {e : _} {pred : A → Set e} → (i : Ideal R pred) → Ideal R2 (inverseImagePred {S = T} {S} {f} (GroupHom.wellDefined (RingHom.groupHom fHom)) (Ideal.isSubset i))
Subgroup.isSubset (Ideal.isSubgroup (inverseImageIsIdeal {T = T} fHom i)) = inverseImageWellDefined {S = T} {S} (GroupHom.wellDefined (RingHom.groupHom fHom)) (Ideal.isSubset i)
Subgroup.closedUnderPlus (Ideal.isSubgroup (inverseImageIsIdeal fHom i)) {g} {h} (c , (prC ,, fg=c)) (d , (prD ,, fh=d)) = (c + d) , (Ideal.closedUnderPlus i prC prD ,, transitive (GroupHom.groupHom (RingHom.groupHom fHom)) (+WellDefined fg=c fh=d))
Subgroup.containsIdentity (Ideal.isSubgroup (inverseImageIsIdeal fHom i)) = 0G , (Ideal.containsIdentity i ,, imageOfIdentityIsIdentity (RingHom.groupHom fHom))
Subgroup.closedUnderInverse (Ideal.isSubgroup (inverseImageIsIdeal fHom i)) (a , (prA ,, fg=a)) = inverse a , (Ideal.closedUnderInverse i prA ,, transitive (homRespectsInverse (RingHom.groupHom fHom)) (inverseWellDefined additiveGroup fg=a))
Ideal.accumulatesTimes (inverseImageIsIdeal {_*2_ = _*2_} {f = f} fHom i) {g} {h} (a , (prA ,, fg=a)) = (a * f h) , (Ideal.accumulatesTimes i prA ,, transitive (RingHom.ringHom fHom) (*WellDefined fg=a reflexive))

memberDividesImpliesMember : {a b : A} → {c : _} → {pred : A → Set c} → (i : Ideal R pred) → pred a → a ∣ b → pred b
memberDividesImpliesMember {a} {b} i pA (s , as=b) = Ideal.isSubset i as=b (Ideal.accumulatesTimes i pA)

generatorZeroImpliesMembersZero : {x : A} → generatedIdealPred R 0R x → x ∼ 0R
generatorZeroImpliesMembersZero {x} (a , b) = transitive (symmetric b) (transitive *Commutative timesZero)
