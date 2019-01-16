{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals
open import Numbers.Integers
open import Numbers.Rationals
open import Groups.Groups
open import Groups.GroupDefinition
open import Rings.RingDefinition
open import Fields.Fields
open import PrimeNumbers
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Fields.FieldOfFractions
open import Fields.FieldOfFractionsOrder
open import Rings.IntegralDomains
open import Rings.RingLemmas

module Numbers.RationalsLemmas where

  triangleInequality : {a b : ℚ} → (absQ (a +Q b)) ≤Q ((absQ a) +Q (absQ b))
  triangleInequality {a} {b} with SetoidTotalOrder.totality ℚTotalOrder 0Q a
  triangleInequality {a} {b} | inl (inl 0<a) with SetoidTotalOrder.totality ℚTotalOrder 0Q b
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) | inl (inl 0<a+b) = inr (reflexive {a +Q b})
    where
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq (fieldOfFractionsSetoid ℤIntDom)))
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) | inl (inr a+b<0) = exFalso (exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} a+b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q +Q 0Q} {0Q} {a +Q b} {a +Q b} (symmetric {0Q} {0Q +Q 0Q} (Group.multIdentRight (Ring.additiveGroup ℚRing) {0Q})) (reflexive {a +Q b}) (ringAddInequalities ℚOrdered {0Q} {a} {0Q} {b} 0<a 0<b)))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inl 0<b) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q +Q 0Q} {0Q} {a +Q b} {0Q} (multIdentRight {0Q}) (symmetric {0Q} {a +Q b} 0=a+b) (ringAddInequalities ℚOrdered {0Q} {a} {0Q} {b} 0<a 0<b)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) | inl (inl 0<a+b) = inl {!!}
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) | inl (inr a+b<0) = inl {!!}
  triangleInequality {a} {b} | inl (inl 0<a) | inl (inr b<0) | inr 0=a+b = inl {!!}
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b | inl (inl 0<a+b) = inr (wellDefined {a} {b} {a} {0Q} (reflexive {a}) (symmetric {0Q} {b} 0=b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} a+b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a} {a +Q b} (reflexive {0Q}) (transitive {a} {a +Q 0Q} {a +Q b} (symmetric {a +Q 0Q} {a} (multIdentRight {a})) (wellDefined {a} {0Q} {a} {b} (reflexive {a}) 0=b)) 0<a)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inl 0<a) | inr 0=b | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {a +Q b} {a} {a +Q b} 0=a+b (transitive {a} {a +Q 0Q} {a +Q b} (symmetric {a +Q 0Q} {a} (multIdentRight {a})) (wellDefined {a} {0Q} {a} {b} (reflexive {a}) 0=b)) 0<a))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inr a<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q b
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) | inl (inl 0<a+b) = inl {!!}
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) | inl (inr a+b<0) = inl {!!}
  triangleInequality {a} {b} | inl (inr a<0) | inl (inl 0<b) | inr 0=a+b = inl {!!}
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {a +Q b} {0Q +Q 0Q} {0Q} (reflexive {a +Q b}) (multIdentRight {0Q}) (ringAddInequalities ℚOrdered {a} {0Q} {b} {0Q} a<0 b<0)) 0<a+b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) | inl (inr a+b<0) = inr (transitive {inverse (fieldOfFractionsPlus ℤIntDom a b)} {fieldOfFractionsPlus ℤIntDom (inverse b) (inverse a)} {fieldOfFractionsPlus ℤIntDom (inverse a) (inverse b)} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}) (Ring.groupIsAbelian ℚRing {inverse b} {inverse a}))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inr a<0) | inl (inr b<0) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {0Q} {0Q} (symmetric {0Q} {a +Q b} 0=a+b) (reflexive {0Q}) (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {a +Q b} {0Q +Q 0Q} {0Q} (reflexive {a +Q b}) (multIdentLeft {0Q}) (ringAddInequalities ℚOrdered {a} {0Q} {b} {0Q} a<0 b<0))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} {0Q} {a} a<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a +Q b} {a} (reflexive {0Q}) (transitive {a +Q b} {a +Q 0Q} {a} (wellDefined {a} {b} {a} {0Q} (reflexive {a}) (symmetric {0Q} {b} 0=b)) (multIdentRight {a})) 0<a+b)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b | inl (inr a+b<0) = inr (transitive {inverse (a +Q b)} {(inverse b) +Q (inverse a)} {(inverse a) +Q 0Q} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}) (transitive {inverse b +Q inverse a} {inverse a +Q inverse b} {inverse a +Q 0Q} (Ring.groupIsAbelian ℚRing {inverse b} {inverse a}) (wellDefined {inverse a} {inverse b} {inverse a} {0Q} (reflexive {inverse a}) (transitive {inverse b} {inverse 0Q} {0Q} (inverseWellDefined (Ring.additiveGroup ℚRing) {b} {0Q} (symmetric {0Q} {b} 0=b)) (symmetric {0Q} {inverse 0Q} (invIdentity (Ring.additiveGroup ℚRing)))))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inl (inr a<0) | inr 0=b | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a} {0Q} {0Q} {0Q} (transitive {a} {a +Q b} {0Q} (transitive {a} {a +Q 0Q} {a +Q b} (symmetric {a +Q 0Q} {a} (multIdentRight {a})) (wellDefined {a} {0Q} {a} {b} (reflexive {a}) 0=b)) (symmetric {0Q} {a +Q b} 0=a+b)) (reflexive {0Q}) a<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a with SetoidTotalOrder.totality ℚTotalOrder 0Q b
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) | inl (inl 0<a+b) = inr (Group.wellDefined (Ring.additiveGroup ℚRing) {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b}))
    where
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {a +Q b} a+b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {b} {a +Q b} (reflexive {0Q}) (transitive {b} {0Q +Q b} {a +Q b} (symmetric {0Q +Q b} {b} (Group.multIdentLeft (Ring.additiveGroup ℚRing) {b})) (Group.wellDefined (Ring.additiveGroup ℚRing) {0Q} {b} {a} {b} 0=a (reflexive {b}))) 0<b)))
    where
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inl (inl 0<b) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {b} {b} {b} (transitive {0Q} {a +Q b} {b} 0=a+b (transitive {a +Q b} {0Q +Q b} {b} (wellDefined {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b})) (multIdentLeft {b}))) (reflexive {b}) 0<b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} {0Q} {b} b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a +Q b} {b} (reflexive {0Q}) (transitive {a +Q b} {0Q +Q b} {b} (wellDefined {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b})) (multIdentLeft {b})) 0<a+b)))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) | inl (inr a+b<0) = inr (transitive {inverse (a +Q b)} {inverse b +Q inverse a} {0Q +Q inverse b} (invContravariant (Ring.additiveGroup ℚRing) {a} {b}) (transitive {inverse b +Q inverse a} {inverse a +Q inverse b} {0Q +Q inverse b} (Ring.groupIsAbelian ℚRing {inverse b} {inverse a}) (wellDefined {inverse a} {inverse b} {0Q} {inverse b} (transitive {inverse a} {inverse 0Q} {0Q} (symmetric {inverse 0Q} {inverse a} (inverseWellDefined (Ring.additiveGroup ℚRing) {0Q} {a} 0=a)) (invIdentity (Ring.additiveGroup ℚRing))) (reflexive {inverse b}))))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inl (inr b<0) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {b} {b} {0Q} {b} (reflexive {b}) (transitive {0Q} {a +Q b} {b} 0=a+b (transitive {a +Q b} {0Q +Q b} {b} (wellDefined {a} {b} {0Q} {b} (symmetric {0Q} {a} 0=a) (reflexive {b})) (multIdentLeft {b}))) b<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inr 0=b with SetoidTotalOrder.totality ℚTotalOrder 0Q (a +Q b)
  triangleInequality {a} {b} | inr 0=a | inr 0=b | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} {0Q} {a +Q b} {0Q} (reflexive {0Q}) (transitive {a +Q b} {0Q +Q 0Q} {0Q} (wellDefined {a} {b} {0Q} {0Q} (symmetric {0Q} {a} 0=a) (symmetric {0Q} {b} 0=b)) (multIdentRight {0Q})) 0<a+b))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inr 0=b | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {0Q} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder ℤIntDom ℤOrderedRing) {a +Q b} {0Q} {0Q} {0Q} (transitive {a +Q b} {0Q +Q 0Q} {0Q} (wellDefined {a} {b} {0Q} {0Q} (symmetric {0Q} {a} 0=a) (symmetric {0Q} {b} 0=b)) (multIdentRight {0Q})) (reflexive {0Q}) a+b<0))
    where
      open Group (Ring.additiveGroup ℚRing)
      open Setoid (fieldOfFractionsSetoid ℤIntDom)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality {a} {b} | inr 0=a | inr 0=b | inr 0=a+b = inr refl

{-
  triangleInequality : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} ({pOrder = pOrder} {tOrder = tOrder} oRing : OrderedRing R tOrder) (I : IntegralDomain R) (x y : fieldOfFractionsSet I) → (fieldOfFractionsComparison I {pOrder = pOrder} {tOrder = tOrder} oRing (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) (fieldOfFractionsPlus I x y)) (fieldOfFractionsPlus I (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) x) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) y))) || (Setoid._∼_ (fieldOfFractionsSetoid I) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) (fieldOfFractionsPlus I x y)) (fieldOfFractionsPlus I (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) x) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) y)))
  triangleInequality {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} {_<_ = _<_} {tOrder = tOrder} {pOrder = pOrder} {tOrder = tOrder} oRing I a b with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) (Ring.0R (fieldOfFractionsRing I)) (numX ,, (denomX , denomX!=0))
  triangleInequality {S = S} {_+_} {_*_} {R} {_<_} {tOrder = tOrder} {pOrder = pOrder} {tOrder = tOrder} oRing I (numX ,, (denomX , denomX!=0)) (numY ,, (denomY , denomY!=0)) | inl (inl 0<x) = {!!}
  triangleInequality {S = S} {_+_} {_*_} {R} {_<_} {tOrder = tOrder} {pOrder = pOrder} {tOrder = tOrder} oRing I (numX ,, (denomX , denomX!=0)) (numY ,, (denomY , denomY!=0)) | inl (inr x<0) = {!!}
  triangleInequality {S = S} {_+_} {_*_} {R} {_<_} {tOrder = tOrder} {pOrder = pOrder} {tOrder = tOrder} oRing I (numX ,, (denomX , denomX!=0)) (numY ,, (denomY , denomY!=0)) | inr 0=x with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I {pOrder = pOrder} {tOrder = tOrder} oRing) (Ring.0R R ,, (Ring.1R R , IntegralDomain.nontrivial I)) (numY ,, (denomY , denomY!=0))
  triangleInequality {S = S} {_+_} {_*_} {R} {_<_} {tOrder = tOrder} {pOrder = pOrder} {tOrder = tOrder} oRing I (numX ,, (denomX , denomX!=0)) (numY ,, (denomY , denomY!=0)) | inr 0=x | inl (inl 0<y) = {!!}
  triangleInequality {S = S} {_+_} {_*_} {R} {_<_} {tOrder = tOrder} {pOrder = pOrder} {tOrder = tOrder} oRing I (numX ,, (denomX , denomX!=0)) (numY ,, (denomY , denomY!=0)) | inr 0=x | inl (inr y<0) = {!!}
  triangleInequality {S = S} {_+_} {_*_} {R} {_<_} {tOrder = tOrder} {pOrder = pOrder} {tOrder = tOrder} oRing I (numX ,, (denomX , denomX!=0)) (numY ,, (denomY , denomY!=0)) | inr 0=x | inr 0=y with = {!!}


  triangleInequality' : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) (I : IntegralDomain R) {x y : fieldOfFractionsSet I} → (fieldOfFractionsComparison I oRing (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) (fieldOfFractionsPlus I x y)) (fieldOfFractionsPlus I (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) x) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) y))) || (Setoid._∼_ (fieldOfFractionsSetoid I) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) (fieldOfFractionsPlus I x y)) (fieldOfFractionsPlus I (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) x) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) y)))
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I oRing) (Ring.0R (fieldOfFractionsRing I)) a
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inl (inl 0<a) with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I oRing) (Ring.0R (fieldOfFractionsRing I)) b
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {fst ,, snd} | inl (inl 0<a) | inl (inl 0<b) = {!!}
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {fst ,, snd} | inl (inl 0<a) | inl (inr b<0) = {!!}
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {fst ,, snd} | inl (inl 0<a) | inr 0=b = {!!}
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inl (inr a<0) = {!!}
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I oRing) (Ring.0R (fieldOfFractionsRing I)) b
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inl 0<b) with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I oRing) (Ring.0R (fieldOfFractionsRing I)) (fieldOfFractionsPlus I a b)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inl 0<b) | inl (inl 0<a+b) = inr (Group.wellDefined (Ring.additiveGroup (fieldOfFractionsRing I)) {a} {b} {Ring.0R (fieldOfFractionsRing I)} {b} (symmetric {Ring.0R (fieldOfFractionsRing I)} {a} 0=a) (reflexive {b}))
    where
      open Setoid (fieldOfFractionsSetoid I)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inl 0<b) | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder I oRing) {fieldOfFractionsPlus I a b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder I oRing) {fieldOfFractionsPlus I a b} {Ring.0R (fieldOfFractionsRing I)} {fieldOfFractionsPlus I a b} a+b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder I oRing) {Ring.0R (fieldOfFractionsRing I)} {(Ring.0R (fieldOfFractionsRing I))} {b} {fieldOfFractionsPlus I a b} (reflexive {(Ring.0R (fieldOfFractionsRing I))}) (transitive {b} {fieldOfFractionsPlus I (Ring.0R (fieldOfFractionsRing I)) b} {fieldOfFractionsPlus I a b} (symmetric {fieldOfFractionsPlus I (Ring.0R (fieldOfFractionsRing I)) b} {b} (Group.multIdentLeft (Ring.additiveGroup (fieldOfFractionsRing I)) {b})) (Group.wellDefined (Ring.additiveGroup (fieldOfFractionsRing I)) {(Ring.0R (fieldOfFractionsRing I))} {b} {a} {b} 0=a (reflexive {b}))) 0<b)))
    where
      open Setoid (fieldOfFractionsSetoid I)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inl 0<b) | inr 0=a+b = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder I oRing) {(Ring.0R (fieldOfFractionsRing I))} {!!})
    where
      open Group (Ring.additiveGroup (fieldOfFractionsRing I))
      open Setoid (fieldOfFractionsSetoid I)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inr b<0) with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I oRing) (Ring.0R (fieldOfFractionsRing I)) (fieldOfFractionsPlus I a b)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inr b<0) | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder I oRing) {b} (SetoidPartialOrder.transitive (fieldOfFractionsOrder I oRing) {b} {(Ring.0R (fieldOfFractionsRing I))} {b} b<0 (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder I oRing) {(Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} {fieldOfFractionsPlus I a b} {b} (reflexive {(Ring.0R (fieldOfFractionsRing I))}) (transitive {fieldOfFractionsPlus I a b} {fieldOfFractionsPlus I (Ring.0R (fieldOfFractionsRing I)) b} {b} (wellDefined {a} {b} {(Ring.0R (fieldOfFractionsRing I))} {b} (symmetric {(Ring.0R (fieldOfFractionsRing I))} {a} 0=a) (reflexive {b})) (multIdentLeft {b})) 0<a+b)))
    where
      open Group (Ring.additiveGroup (fieldOfFractionsRing I))
      open Setoid (fieldOfFractionsSetoid I)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inr b<0) | inl (inr a+b<0) = inr {!!}
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inl (inr b<0) | inr 0=a+b = exFalso {!!}
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inr 0=b with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder I oRing) (Ring.0R (fieldOfFractionsRing I)) (fieldOfFractionsPlus I a b)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inr 0=b | inl (inl 0<a+b) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder I oRing) {(Ring.0R (fieldOfFractionsRing I))} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder I oRing) {(Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} {fieldOfFractionsPlus I a b} {(Ring.0R (fieldOfFractionsRing I))} (reflexive {(Ring.0R (fieldOfFractionsRing I))}) (transitive {fieldOfFractionsPlus I a b} {fieldOfFractionsPlus I (Ring.0R (fieldOfFractionsRing I)) (Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} (wellDefined {a} {b} {(Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} (symmetric {(Ring.0R (fieldOfFractionsRing I))} {a} 0=a) (symmetric {(Ring.0R (fieldOfFractionsRing I))} {b} 0=b)) (multIdentRight {(Ring.0R (fieldOfFractionsRing I))})) 0<a+b))
    where
      open Group (Ring.additiveGroup (fieldOfFractionsRing I))
      open Setoid (fieldOfFractionsSetoid I)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inr 0=b | inl (inr a+b<0) = exFalso (SetoidPartialOrder.irreflexive (fieldOfFractionsOrder I oRing) {(Ring.0R (fieldOfFractionsRing I))} (SetoidPartialOrder.wellDefined (fieldOfFractionsOrder I oRing) {fieldOfFractionsPlus I a b} {(Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} (transitive {fieldOfFractionsPlus I a b} {fieldOfFractionsPlus I (Ring.0R (fieldOfFractionsRing I)) (Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} (wellDefined {a} {b} {(Ring.0R (fieldOfFractionsRing I))} {(Ring.0R (fieldOfFractionsRing I))} (symmetric {(Ring.0R (fieldOfFractionsRing I))} {a} 0=a) (symmetric {(Ring.0R (fieldOfFractionsRing I))} {b} 0=b)) (multIdentRight {(Ring.0R (fieldOfFractionsRing I))})) (reflexive {(Ring.0R (fieldOfFractionsRing I))}) a+b<0))
    where
      open Group (Ring.additiveGroup (fieldOfFractionsRing I))
      open Setoid (fieldOfFractionsSetoid I)
      open Symmetric (Equivalence.symmetricEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Transitive (Equivalence.transitiveEq eq)
  triangleInequality' {pOrder = pOrder} {tOrder = tOrder} oRing I {a} {b} | inr 0=a | inr 0=b | inr 0=a+b = inr {!!}

-}
