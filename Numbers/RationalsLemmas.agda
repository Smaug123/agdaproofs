{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Integers
open import Numbers.Rationals
open import Groups.Groups
open import Groups.Lemmas
open import Groups.Definition
open import Rings.Definition
open import Fields.Fields
open import PrimeNumbers
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Fields.FieldOfFractions
open import Fields.FieldOfFractionsOrder
open import Rings.IntegralDomains
open import Rings.Lemmas
open import Sets.EquivalenceRelations

module Numbers.RationalsLemmas where

  triangleInequality : {a b : ℚ} → (absQ (a +Q b)) ≤Q ((absQ a) +Q (absQ b))
  triangleInequality {a} {b} with SetoidTotalOrder.totality ℚTotalOrder 0Q a
  triangleInequality {a} {b} | inl (inl 0<a) with SetoidTotalOrder.totality ℚTotalOrder 0Q b
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) | inl (inl 0<a+b) = inr (reflexive {a +Q b})
    where
      open Equivalence (Setoid.eq (fieldOfFractionsSetoid ℤIntDom))
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) | inl (inr a+b<0) = exFalso (exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} a+b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q +Q 0Q} {0Q} {a +Q b} {a +Q b} (symmetric {0Q} {0Q +Q 0Q} (Group.multIdentRight (Ring.additiveGroup ℚRing) {0Q})) (reflexive {a +Q b}) (ringAddInequalities ℚOrdered {0Q} {a} {0Q} {b} 0<a 0<b)))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q +Q 0Q} {0Q} {a +Q b} {0Q} (multIdentRight {0Q}) (symmetric {0Q} {a +Q b} 0=a+b) (ringAddInequalities ℚOrdered {0Q} {a} {0Q} {b} 0<a 0<b)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) | inl (inl 0<a+b) = inl (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b +Q a} {a +Q b} {inverse b +Q a} {a +Q inverse b} (Ring.groupIsAbelian ℚRing {b} {a}) (Ring.groupIsAbelian ℚRing {inverse b} {a}) (OrderedRing.orderRespectsAddition ℚOrdered {b} {inverse b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} {0Q} {inverse b} b<0 (ringMinusFlipsOrder'' ℚOrdered {b} b<0)) a))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) | inl (inr a+b<0) = inl (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {inverse a +Q inverse b} {inverse (a +Q b)} {a +Q inverse b} {a +Q inverse b} (transitive {inverse a +Q inverse b} {inverse b +Q inverse a} {inverse (a +Q b)} (Ring.groupIsAbelian ℚRing {inverse a} {inverse b}) (symmetric {inverse (a +Q b)} {inverse b +Q inverse a} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}))) (reflexive {a +Q inverse b}) (OrderedRing.orderRespectsAddition ℚOrdered {inverse a} {a} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {inverse a} {0Q} {a} (ringMinusFlipsOrder ℚOrdered {a} 0<a) 0<a) (inverse b)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) | inr 0=a+b = inl (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {a} {a +Q (inverse b)} 0<a (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q +Q a} {a} {inverse b +Q a} {a +Q inverse b} (multIdentLeft {a}) (Ring.groupIsAbelian ℚRing {inverse b} {a}) (OrderedRing.orderRespectsAddition ℚOrdered {0Q} {inverse b} (ringMinusFlipsOrder'' ℚOrdered {b} b<0) a)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b | inl (inl 0<a+b) = inr (wellDefined {a} {b} {a} {0Q} (reflexive {a}) (symmetric {0Q} {b} 0=b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} a+b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a} {a +Q b} (reflexive {0Q}) (transitive {a} {a +Q 0Q} {a +Q b} (symmetric {a +Q 0Q} {a} (multIdentRight {a})) (wellDefined {a} {0Q} {a} {b} (reflexive {a}) 0=b)) 0<a)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {a +Q b} {a} {a +Q b} 0=a+b (transitive {a} {a +Q 0Q} {a +Q b} (symmetric {a +Q 0Q} {a} (multIdentRight {a})) (wellDefined {a} {0Q} {a} {b} (reflexive {a}) 0=b)) 0<a))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q b
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) | inl (inl 0<a+b) = inl (OrderedRing.orderRespectsAddition ℚOrdered {a} {inverse a} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} {0Q} {inverse a} a<0 (ringMinusFlipsOrder'' ℚOrdered {a} a<0)) b)
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) | inl (inr a+b<0) = inl (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {inverse a +Q inverse b} {inverse (a +Q b)} {inverse a +Q b} {inverse a +Q b} (transitive {inverse a +Q inverse b} {inverse b +Q inverse a} {inverse (a +Q b)} (Ring.groupIsAbelian ℚRing {inverse a} {inverse b}) (symmetric {inverse (a +Q b)} {inverse b +Q inverse a} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}))) (reflexive {inverse a +Q b}) blah)
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
      blah : (inverse a +Q inverse b) <Q (inverse a +Q b)
      blah = SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {inverse b +Q inverse a} {inverse a +Q inverse b} {b +Q inverse a} {inverse a +Q b} (Ring.groupIsAbelian ℚRing {inverse b} {inverse a}) (Ring.groupIsAbelian ℚRing {b} {inverse a}) (OrderedRing.orderRespectsAddition ℚOrdered {inverse b} {b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {inverse b} {0Q} {b} (ringMinusFlipsOrder ℚOrdered {b} 0<b) 0<b) (inverse a))
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) | inr 0=a+b = inl (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {b} {inverse a +Q b} 0<b (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b +Q 0Q} {b} {b +Q inverse a} {inverse a +Q b} (multIdentRight {b}) (Ring.groupIsAbelian ℚRing {b} {inverse a}) (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q +Q b} {b +Q 0Q} {inverse a +Q b} {b +Q inverse a} (Ring.groupIsAbelian ℚRing {0Q} {b}) (Ring.groupIsAbelian ℚRing {inverse a} {b}) (OrderedRing.orderRespectsAddition ℚOrdered {0Q} {inverse a} (ringMinusFlipsOrder'' ℚOrdered {a} a<0) b))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {a +Q b} {0Q +Q 0Q} {0Q} (reflexive {a +Q b}) (multIdentRight {0Q}) (ringAddInequalities ℚOrdered {a} {0Q} {b} {0Q} a<0 b<0)) 0<a+b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) | inl (inr a+b<0) = inr (transitive {inverse (fieldOfFractionsPlus ℤIntDom a b)} {fieldOfFractionsPlus ℤIntDom (inverse b) (inverse a)} {fieldOfFractionsPlus ℤIntDom (inverse a) (inverse b)} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}) (Ring.groupIsAbelian ℚRing {inverse b} {inverse a}))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {0Q} {0Q} (symmetric {0Q} {a +Q b} 0=a+b) (reflexive {0Q}) (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {a +Q b} {0Q +Q 0Q} {0Q} (reflexive {a +Q b}) (multIdentLeft {0Q}) (ringAddInequalities ℚOrdered {a} {0Q} {b} {0Q} a<0 b<0))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} {0Q} {a} a<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a +Q b} {a} (reflexive {0Q}) (transitive {a +Q b} {a +Q 0Q} {a} (wellDefined {a} {b} {a} {0Q} (reflexive {a}) (symmetric {0Q} {b} 0=b)) (multIdentRight {a})) 0<a+b)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b | inl (inr a+b<0) = inr (transitive {inverse (a +Q b)} {(inverse b) +Q (inverse a)} {(inverse a) +Q 0Q} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}) (transitive {inverse b +Q inverse a} {inverse a +Q inverse b} {inverse a +Q 0Q} (Ring.groupIsAbelian ℚRing {inverse b} {inverse a}) (wellDefined {inverse a} {inverse b} {inverse a} {0Q} (reflexive {inverse a}) (transitive {inverse b} {inverse 0Q} {0Q} (inverseWellDefined (Ring.additiveGroup ℚRing) {b} {0Q} (symmetric {0Q} {b} 0=b)) (symmetric {0Q} {inverse 0Q} (invIdentity (Ring.additiveGroup ℚRing)))))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} {0Q} {0Q} {0Q} (transitive {a} {a +Q b} {0Q} (transitive {a} {a +Q 0Q} {a +Q b} (symmetric {a +Q 0Q} {a} (multIdentRight {a})) (wellDefined {a} {0Q} {a} {b} (reflexive {a}) 0=b)) (symmetric {0Q} {a +Q b} 0=a+b)) (reflexive {0Q}) a<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a with SetoidTotalOrder.totality ℚTotalOrder 0Q b
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) | inl (inl 0<a+b) = inr (Group.wellDefined (Ring.additiveGroup ℚRing) {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b}))
    where
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} a+b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {b} {a +Q b} (reflexive {0Q}) (transitive {b} {0Q +Q b} {a +Q b} (symmetric {0Q +Q b} {b} (Group.multIdentLeft (Ring.additiveGroup ℚRing) {b})) (Group.wellDefined (Ring.additiveGroup ℚRing) {0Q} {b} {a} {b} 0=a (reflexive {b}))) 0<b)))
    where
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {b} {b} {b} (transitive {0Q} {a +Q b} {b} 0=a+b (transitive {a +Q b} {0Q +Q b} {b} (wellDefined {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b})) (multIdentLeft {b}))) (reflexive {b}) 0<b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} {0Q} {b} b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a +Q b} {b} (reflexive {0Q}) (transitive {a +Q b} {0Q +Q b} {b} (wellDefined {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b})) (multIdentLeft {b})) 0<a+b)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) | inl (inr a+b<0) = inr (transitive {inverse (a +Q b)} {inverse b +Q inverse a} {0Q +Q inverse b} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}) (transitive {inverse b +Q inverse a} {inverse a +Q inverse b} {0Q +Q inverse b} (Ring.groupIsAbelian ℚRing {inverse b} {inverse a}) (wellDefined {inverse a} {inverse b} {0Q} {inverse b} (transitive {inverse a} {inverse 0Q} {0Q} (symmetric {inverse 0Q} {inverse a} (inverseWellDefined (Ring.additiveGroup ℚRing) {0Q} {a} 0=a)) (invIdentity (Ring.additiveGroup ℚRing))) (reflexive {inverse b}))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} {b} {0Q} {b} (reflexive {b}) (transitive {0Q} {a +Q b} {b} 0=a+b (transitive {a +Q b} {0Q +Q b} {b} (wellDefined {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b})) (multIdentLeft {b}))) b<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inr 0=b with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inr 0=a | inr 0=b | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a +Q b} {0Q} (reflexive {0Q}) (transitive {a +Q b} {0Q +Q 0Q} {0Q} (wellDefined {a} {b} {0Q} {0Q} (symmetric {0Q} {a} 0=a) (symmetric {0Q} {b} 0=b)) (multIdentRight {0Q})) 0<a+b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inr 0=b | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {0Q} {0Q} (transitive {a +Q b} {0Q +Q 0Q} {0Q} (wellDefined {a} {b} {0Q} {0Q} (symmetric {0Q} {a} 0=a) (symmetric {0Q} {b} 0=b)) (multIdentRight {0Q})) (reflexive {0Q}) a+b<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  triangleInequality {a} {b} | inr 0=a | inr 0=b | inr 0=a+b = inr refl

  absNegation : (a : ℚ) → ((absQ a) =Q (absQ (negateQ a)))
  absNegation a with SetoidTotalOrder.totality ℚTotalOrder 0Q a
  absNegation a | inl (inl 0<a) with SetoidTotalOrder.totality ℚTotalOrder 0Q (negateQ a)
  absNegation a | inl (inl 0<a) | inl (inl 0<-a) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} {0Q} {a} (ringMinusFlipsOrder''' ℚOrdered {a} 0<-a) 0<a))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  absNegation a | inl (inl 0<a) | inl (inr _) = symmetric {inverse (inverse a)} {a} (invTwice (Ring.additiveGroup ℚRing) a)
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  absNegation a | inl (inl 0<a) | inr 0=-a = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a} {0Q} (reflexive {0Q}) (transitive {a} {inverse 0Q} {0Q} (swapInv (Ring.additiveGroup ℚRing) {a} {0Q} (symmetric {0Q} {inverse a} 0=-a)) (invIdentity (Ring.additiveGroup ℚRing))) 0<a))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  absNegation a | inl (inr a<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q (negateQ a)
  absNegation a | inl (inr a<0) | inl (inl _) = Equivalence.reflexive (Setoid.eq (fieldOfFractionsSetoid ℤIntDom)) {Group.inverse (Ring.additiveGroup ℚRing) a}
  absNegation a | inl (inr a<0) | inl (inr -a<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {a} {0Q} (ringMinusFlipsOrder' ℚOrdered {a} -a<0) a<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  absNegation a | inl (inr a<0) | inr -a=0 = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} {0Q} {0Q} {0Q} (transitive {a} {inverse 0Q} {0Q} (swapInv (Ring.additiveGroup ℚRing) {a} {0Q} (symmetric {0Q} {inverse a} -a=0)) (invIdentity (Ring.additiveGroup ℚRing))) (reflexive {0Q}) a<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  absNegation a | inr 0=a with SetoidTotalOrder.totality ℚTotalOrder 0Q (negateQ a)
  absNegation a | inr 0=a | inl (inl 0<-a) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {inverse a} {0Q} (reflexive {0Q}) (transitive {inverse a} {inverse 0Q} {0Q} (symmetric {inverse 0Q} {inverse a} (inverseWellDefined (Ring.additiveGroup ℚRing) {0Q} {a} 0=a)) (invIdentity (Ring.additiveGroup ℚRing))) 0<-a))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  absNegation a | inr 0=a | inl (inr -a<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {inverse a} {0Q} {0Q} {0Q} (transitive {inverse a} {inverse 0Q} {0Q} (symmetric {inverse 0Q} {inverse a} (inverseWellDefined (Ring.additiveGroup ℚRing) {0Q} {a} 0=a)) (invIdentity (Ring.additiveGroup ℚRing))) (reflexive {0Q}) -a<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Equivalence eq
  absNegation a | inr 0=a | inr _ = refl
