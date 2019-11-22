{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Subgroups.Definition
open import Rings.Homomorphisms.Kernel
open import Rings.Cosets

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Rings.Ideals.Definition R

idealPredForKernel : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → A → Set d
idealPredForKernel {T = T} R2 {f} fHom a = Setoid._∼_ T (f a) (Ring.0R R2)

idealPredForKernelWellDefined : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → {x y : A} → (Setoid._∼_ S x y) → (idealPredForKernel R2 fHom x → idealPredForKernel R2 fHom y)
idealPredForKernelWellDefined {T = T} R2 {f} fHom a x=0 = Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined (RingHom.groupHom fHom) (Equivalence.symmetric (Setoid.eq S) a)) x=0

kernelIdealIsIdeal : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} {R2 : Ring T _+2_ _*2_} {f : A → C} (fHom : RingHom R R2 f) → Ideal (idealPredForKernel R2 fHom)
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

open Setoid S
open Ring R
open Group additiveGroup
open Equivalence eq
open import Groups.Lemmas additiveGroup

idealIsKernelMap : {c : _} {pred : A → Set c} → (i : Ideal pred) → {x : A} → pred x → ringKernel {R1 = R} {R2 = cosetRing R i} (cosetRingHom R i)
idealIsKernelMap {c} {pred} i {x} predX = x , (Ideal.isSubset i (transitive (symmetric identLeft) (+WellDefined (symmetric invIdent) reflexive)) predX)
