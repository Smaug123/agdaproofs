{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Integers
open import Groups.Groups
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Fields.Fields
open import Numbers.Primes.PrimeNumbers
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Sets.EquivalenceRelations

module Numbers.Rationals.Definition where

open import Fields.FieldOfFractions.Setoid ℤIntDom
open import Fields.FieldOfFractions.Addition ℤIntDom
open import Fields.FieldOfFractions.Multiplication ℤIntDom
open import Fields.FieldOfFractions.Ring ℤIntDom
open import Fields.FieldOfFractions.Field ℤIntDom
open import Fields.FieldOfFractions.Order ℤIntDom ℤOrderedRing

ℚ : Set
ℚ = fieldOfFractionsSet

_+Q_ : ℚ → ℚ → ℚ
a +Q b = fieldOfFractionsPlus a b

_*Q_ : ℚ → ℚ → ℚ
a *Q b = fieldOfFractionsTimes a b

ℚRing : Ring fieldOfFractionsSetoid _+Q_ _*Q_
ℚRing = fieldOfFractionsRing

0Q : ℚ
0Q = Ring.0R ℚRing

injectionQ : ℤ → ℚ
injectionQ z = z ,, (nonneg 1 , λ ())

ℚField : Field ℚRing
ℚField = fieldOfFractions

_<Q_ : ℚ → ℚ → Set
_<Q_ = fieldOfFractionsComparison

_=Q_ : ℚ → ℚ → Set
a =Q b = Setoid._∼_ fieldOfFractionsSetoid a b

reflQ : {x : ℚ} → (x =Q x)
reflQ {x} = Equivalence.reflexive (Setoid.eq fieldOfFractionsSetoid) {x}

_≤Q_ : ℚ → ℚ → Set
a ≤Q b = (a <Q b) || (a =Q b)

negateQ : ℚ → ℚ
negateQ a = Group.inverse (Ring.additiveGroup ℚRing) a

_-Q_ : ℚ → ℚ → ℚ
a -Q b = a +Q negateQ b

a-A : (a : ℚ) → (a -Q a) =Q 0Q
a-A a = Group.invRight (Ring.additiveGroup ℚRing) {a}

ℚPartialOrder : SetoidPartialOrder fieldOfFractionsSetoid fieldOfFractionsComparison
ℚPartialOrder = fieldOfFractionsOrder

ℚTotalOrder : SetoidTotalOrder fieldOfFractionsOrder
ℚTotalOrder = fieldOfFractionsTotalOrder

open SetoidTotalOrder fieldOfFractionsTotalOrder
open SetoidPartialOrder partial
open Setoid fieldOfFractionsSetoid

negateQWellDefined : (a b : ℚ) → (a =Q b) → (negateQ a) =Q (negateQ b)
negateQWellDefined a b a=b = inverseWellDefined (Ring.additiveGroup ℚRing) {a} {b} a=b

ℚPOrdered : PartiallyOrderedRing ℚRing partial
ℚPOrdered = fieldOfFractionsPOrderedRing

ℚOrdered : TotallyOrderedRing ℚPOrdered
ℚOrdered = fieldOfFractionsOrderedRing

ℚcharNot2 : ((Ring.1R ℚRing) +Q (Ring.1R ℚRing)) =Q (Ring.0R ℚRing) → False
ℚcharNot2 ()
