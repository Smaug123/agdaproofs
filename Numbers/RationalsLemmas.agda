{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals
open import Numbers.Integers
open import Numbers.Rationals
open import Groups.Groups
open import Rings.RingDefinition
open import Fields.Fields
open import PrimeNumbers
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Fields.FieldOfFractions
open import Fields.FieldOfFractionsOrder
open import Rings.IntegralDomains

module Numbers.RationalsLemmas where
  triangleInequality : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {tOrder : SetoidTotalOrder pOrder} (oRing : OrderedRing R tOrder) (I : IntegralDomain R) (x y : fieldOfFractionsSet I) → (fieldOfFractionsComparison I oRing (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) (fieldOfFractionsPlus I x y)) (fieldOfFractionsPlus I (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) x) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) y))) || (Setoid._∼_ (fieldOfFractionsSetoid I) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) (fieldOfFractionsPlus I x y)) (fieldOfFractionsPlus I (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) x) (abs (fieldOfFractionsRing I) (fieldOfFractionsTotalOrder I oRing) y)))
  triangleInequality {R = R} {tOrder = tOrder} oRing I (numX ,, (denomX , denomX!=0)) (numY ,, (denomY , denomY!=0)) = {!!}
