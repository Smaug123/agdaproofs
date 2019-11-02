{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Integers
open import Groups.Groups
open import Groups.Definition
open import Rings.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Fields.Fields
open import Numbers.Primes.PrimeNumbers
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Fields.FieldOfFractions
open import Fields.FieldOfFractionsOrder
open import Sets.EquivalenceRelations

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

injectionQ : ℤ → ℚ
injectionQ z = z ,, (nonneg 1 , λ ())

ℚField : Field ℚRing
ℚField = fieldOfFractions ℤIntDom

_<Q_ : ℚ → ℚ → Set
_<Q_ = fieldOfFractionsComparison ℤIntDom ℤOrderedRing

_=Q_ : ℚ → ℚ → Set
a =Q b = Setoid._∼_ (fieldOfFractionsSetoid ℤIntDom) a b

reflQ : {x : ℚ} → (x =Q x)
reflQ {x} = Equivalence.reflexive (Setoid.eq (fieldOfFractionsSetoid ℤIntDom)) {x}

_≤Q_ : ℚ → ℚ → Set
a ≤Q b = (a <Q b) || (a =Q b)

negateQ : ℚ → ℚ
negateQ a = Group.inverse (Ring.additiveGroup ℚRing) a

_-Q_ : ℚ → ℚ → ℚ
a -Q b = a +Q negateQ b

a-A : (a : ℚ) → (a -Q a) =Q 0Q
a-A a = Group.invRight (Ring.additiveGroup ℚRing) {a}

ℚPartialOrder : SetoidPartialOrder (fieldOfFractionsSetoid ℤIntDom) (fieldOfFractionsComparison ℤIntDom ℤOrderedRing)
ℚPartialOrder = fieldOfFractionsOrder ℤIntDom ℤOrderedRing

ℚTotalOrder : SetoidTotalOrder (fieldOfFractionsOrder ℤIntDom ℤOrderedRing)
ℚTotalOrder = fieldOfFractionsTotalOrder ℤIntDom ℤOrderedRing

open SetoidTotalOrder (fieldOfFractionsTotalOrder ℤIntDom ℤOrderedRing)
open SetoidPartialOrder partial
open Setoid (fieldOfFractionsSetoid ℤIntDom)

negateQWellDefined : (a b : ℚ) → (a =Q b) → (negateQ a) =Q (negateQ b)
negateQWellDefined a b a=b = inverseWellDefined (Ring.additiveGroup ℚRing) {a} {b} a=b

ℚPOrdered : PartiallyOrderedRing ℚRing partial
ℚPOrdered = fieldOfFractionsPOrderedRing ℤIntDom ℤOrderedRing

ℚOrdered : TotallyOrderedRing ℚPOrdered
ℚOrdered = fieldOfFractionsOrderedRing ℤIntDom ℤOrderedRing
