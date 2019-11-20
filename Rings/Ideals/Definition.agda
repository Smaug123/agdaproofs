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

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open import Groups.Subgroups.Definition (Ring.additiveGroup R)

ringKernel : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → Set (a ⊔ d)
ringKernel {T = T} R2 {f} fHom = Sg A (λ a → Setoid._∼_ T (f a) (Ring.0R R2))

ideal : {c : _} (pred : A → Set c) → Set (a ⊔ b ⊔ c)
ideal pred = subgroup pred && ({x : A} → {y : A} → pred x → pred (x * y))

idealPredForKernel : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → A → Set d
idealPredForKernel {T = T} R2 {f} fHom a = Setoid._∼_ T (f a) (Ring.0R R2)

idealPredForKernelWellDefined : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} (R2 : Ring T _+2_ _*2_) {f : A → C} (fHom : RingHom R R2 f) → {x y : A} → (Setoid._∼_ S x y) → (idealPredForKernel R2 fHom x → idealPredForKernel R2 fHom y)
idealPredForKernelWellDefined {T = T} R2 {f} fHom a x=0 = Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined (RingHom.groupHom fHom) (Equivalence.symmetric (Setoid.eq S) a)) x=0

kernelIdealIsIdeal : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+2_ _*2_ : C → C → C} {R2 : Ring T _+2_ _*2_} {f : A → C} (fHom : RingHom R R2 f) → ideal (idealPredForKernel R2 fHom)
_&&_.fst (_&&_.fst (kernelIdealIsIdeal {R2 = R2} fHom)) = idealPredForKernelWellDefined R2 fHom
_&_&_.one (_&&_.snd (_&&_.fst (kernelIdealIsIdeal {T = T} {R2 = R2} fHom))) {x} {y} fx=0 fy=0 = transitive (transitive (GroupHom.groupHom (RingHom.groupHom fHom)) (+WellDefined fx=0 fy=0)) identLeft
  where
    open Ring R2
    open Group (Ring.additiveGroup R2)
    open Setoid T
    open Equivalence eq
_&_&_.two (_&&_.snd (_&&_.fst (kernelIdealIsIdeal fHom))) = imageOfIdentityIsIdentity (RingHom.groupHom fHom)
_&_&_.three (_&&_.snd (_&&_.fst (kernelIdealIsIdeal {T = T} {R2 = R2} fHom))) {x} fx=0 = zeroImpliesInverseZero (RingHom.groupHom fHom) fx=0
  where
    open Ring R2
    open Group (Ring.additiveGroup R2)
    open Setoid T
    open Equivalence eq
_&&_.snd (kernelIdealIsIdeal {T = T} {R2 = R2} {f = f} fHom) {x} {y} fx=0 = transitive (RingHom.ringHom fHom) (transitive (Ring.*WellDefined R2 fx=0 reflexive) (transitive (Ring.*Commutative R2) (Ring.timesZero R2 {f y})))
  where
    open Setoid T
    open Equivalence eq

-- TODO : define the quotient by an ideal; note that the result is a ring
