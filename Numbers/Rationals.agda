{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Integers
open import Groups.Groups
open import Groups.Definition
open import Rings.Definition
open import Fields.Fields
open import PrimeNumbers
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Fields.FieldOfFractions
open import Fields.FieldOfFractionsOrder

module Numbers.Rationals where

  ℚ : Set
  ℚ = fieldOfFractionsSet ℤIntDom

  _+Q_ : ℚ → ℚ → ℚ
  a +Q b = fieldOfFractionsPlus ℤIntDom a b

  _*Q_ : ℚ → ℚ → ℚ
  a *Q b = fieldOfFractionsTimes ℤIntDom a b

  ℚRing : Ring (fieldOfFractionsSetoid ℤIntDom) _+Q_ _*Q_
  ℚRing = fieldOfFractionsRing ℤIntDom

  0Q : ℚ
  0Q = Ring.0R ℚRing

  ℚField : Field ℚRing
  ℚField = fieldOfFractions ℤIntDom

  _<Q_ : ℚ → ℚ → Set
  _<Q_ = fieldOfFractionsComparison ℤIntDom ℤOrderedRing

  _=Q_ : ℚ → ℚ → Set
  a =Q b = Setoid._∼_ (fieldOfFractionsSetoid ℤIntDom) a b

  reflQ : {x : ℚ} → (x =Q x)
  reflQ {x} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (fieldOfFractionsSetoid ℤIntDom))) {x}

  _≤Q_ : ℚ → ℚ → Set
  a ≤Q b = (a <Q b) || (a =Q b)

  negateQ : ℚ → ℚ
  negateQ a = Group.inverse (Ring.additiveGroup ℚRing) a

  _-Q_ : ℚ → ℚ → ℚ
  a -Q b = a +Q negateQ b

  ℚPartialOrder : SetoidPartialOrder (fieldOfFractionsSetoid ℤIntDom) (fieldOfFractionsComparison ℤIntDom ℤOrderedRing)
  ℚPartialOrder = fieldOfFractionsOrder ℤIntDom ℤOrderedRing

  ℚTotalOrder : SetoidTotalOrder (fieldOfFractionsOrder ℤIntDom ℤOrderedRing)
  ℚTotalOrder = fieldOfFractionsTotalOrder ℤIntDom ℤOrderedRing

  absQ : ℚ → ℚ
  absQ q with SetoidTotalOrder.totality (fieldOfFractionsTotalOrder ℤIntDom ℤOrderedRing) 0Q q
  absQ q | inl (inl 0<q) = q
  absQ q | inl (inr q<0) = Group.inverse (Ring.additiveGroup ℚRing) q
  absQ q | inr x = 0Q

  ℚOrdered : OrderedRing ℚRing (fieldOfFractionsTotalOrder ℤIntDom ℤOrderedRing)
  ℚOrdered = fieldOfFractionsOrderedRing ℤIntDom ℤOrderedRing
