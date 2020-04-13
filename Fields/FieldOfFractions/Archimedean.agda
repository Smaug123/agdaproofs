{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.Naturals.Semiring
open import Functions
open import LogicalFormulae
open import Groups.Definition
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Setoids.Orders
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition

module Fields.FieldOfFractions.Archimedean {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) {c : _} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) where

open import Groups.Cyclic.Definition
open import Fields.FieldOfFractions.Setoid I
open import Fields.FieldOfFractions.Group I
open import Fields.FieldOfFractions.Addition I
open import Fields.FieldOfFractions.Ring I
open import Fields.FieldOfFractions.Order I order
open import Rings.Orders.Partial.Archimedean

private

  simpPower : (n : ℕ) → Setoid._∼_ fieldOfFractionsSetoid (positiveEltPower fieldOfFractionsGroup (Ring.1R R ,, (Ring.1R R , IntegralDomain.nontrivial I)) n) ((positiveEltPower (Ring.additiveGroup R) (Ring.1R R) n) ,, ((Ring.1R R) , IntegralDomain.nontrivial I))
  simpPower zero = Equivalence.reflexive (Setoid.eq fieldOfFractionsSetoid) {Group.0G fieldOfFractionsGroup}
  simpPower (succ n) = transitive (+WellDefined {{!!}} {{!!}} {{!!}} {{!!}} (reflexive {Ring.1R R ,, (Ring.1R R , IntegralDomain.nontrivial I)}) (simpPower n)) {!!}
    where
      open Setoid fieldOfFractionsSetoid
      open Equivalence eq
      open Ring fieldOfFractionsRing
      open Group additiveGroup

open Setoid S
open Equivalence eq
open Ring R
open Group additiveGroup
open TotallyOrderedRing order
open SetoidTotalOrder total

private

-- TODO: this whole thing will be easier going via Archimedean in the groups sense.
-- Find n such that num < denom * n; then num/denom < n.
  lemma : (n : ℕ) {num denom : A} (d!=0 : denom ∼ 0G → False) → (num * denom) < positiveEltPower additiveGroup 1R n → fieldOfFractionsComparison (num ,, (denom , d!=0)) (positiveEltPower fieldOfFractionsGroup (1R ,, (1R , IntegralDomain.nontrivial I)) n)
  lemma n {num} {d} d!=0 pr with totality 0R d
  ... | inl (inl 0<d) = {!!}
  ... | inl (inr d<0) = {!!}
  ... | inr x = exFalso (d!=0 (symmetric x))

fieldOfFractionsArchimedean : ArchimedeanRing pRing → ArchimedeanRing fieldOfFractionsPOrderedRing
fieldOfFractionsArchimedean arch (num ,, (denom , denom!=0)) with arch (num * denom)
... | N , pr = N , lemma N denom!=0 pr
