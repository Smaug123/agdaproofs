{-# OPTIONS --safe --warning=error --without-K #-}

open import Numbers.Naturals.Semiring
open import Functions
open import LogicalFormulae
open import Groups.Definition
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Orders.Archimedean

module Fields.FieldOfFractions.Archimedean {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) {c : _} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (nonempty : (Setoid._∼_ S (Ring.0R R) (Ring.1R R)) → False) where

open import Groups.Cyclic.Definition
open import Fields.FieldOfFractions.Setoid I
open import Fields.FieldOfFractions.Group I
open import Fields.FieldOfFractions.Addition I
open import Fields.FieldOfFractions.Ring I
open import Fields.FieldOfFractions.Order I order
open import Fields.FieldOfFractions.Field I
open import Fields.Orders.Total.Archimedean
open import Rings.Orders.Partial.Lemmas pRing
open import Rings.Orders.Total.Lemmas order

open Setoid S
open Equivalence eq
open Ring R
open Group additiveGroup
open TotallyOrderedRing order
open SetoidTotalOrder total

private

  denomPower : (n : ℕ) → fieldOfFractionsSet.denom (positiveEltPower fieldOfFractionsGroup record { num = 1R ; denom = 1R ; denomNonzero = IntegralDomain.nontrivial I } n) ∼ 1R
  denomPower zero = reflexive
  denomPower (succ n) = transitive identIsIdent (denomPower n)

  denomPlus : {a : A} .(a!=0 : a ∼ 0R → False) (n1 n2 : A) → Setoid._∼_ fieldOfFractionsSetoid (fieldOfFractionsPlus record { num = n1 ; denom = a ; denomNonzero = a!=0 } record { num = n2 ; denom = a ; denomNonzero = a!=0 }) (record { num = n1 + n2 ; denom = a ; denomNonzero = a!=0 })
  denomPlus {a} a!=0 n1 n2 = transitive *Commutative (transitive (*WellDefined reflexive (transitive (+WellDefined *Commutative reflexive) (symmetric *DistributesOver+))) *Associative)

  d : (a : fieldOfFractionsSet) → fieldOfFractionsSet.denom a ∼ 0R → False
  d record { num = num ; denom = denom ; denomNonzero = denomNonzero } bad = exFalso (denomNonzero bad)

  simpPower : (n : ℕ) → Setoid._∼_ fieldOfFractionsSetoid (positiveEltPower fieldOfFractionsGroup record { num = Ring.1R R ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I} n) record { num = positiveEltPower (Ring.additiveGroup R) (Ring.1R R) n ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I }
  simpPower zero = Equivalence.reflexive (Setoid.eq fieldOfFractionsSetoid) {Group.0G fieldOfFractionsGroup}
  simpPower (succ n) = Equivalence.transitive (Setoid.eq fieldOfFractionsSetoid) {record { denomNonzero = d (fieldOfFractionsPlus (record { num = 1R ; denom = 1R ; denomNonzero = λ t → nonempty (symmetric t) }) (positiveEltPower fieldOfFractionsGroup _ n)) }} {record { denomNonzero = λ t → nonempty (symmetric (transitive (symmetric identIsIdent) t)) }} {record { denomNonzero = λ t → nonempty (symmetric t) }} (Group.+WellDefined fieldOfFractionsGroup {record { num = Ring.1R R ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I }} {positiveEltPower fieldOfFractionsGroup record { num = Ring.1R R ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I } n} {record { num = Ring.1R R ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I }} {record { num = positiveEltPower (Ring.additiveGroup R) (Ring.1R R) n ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I }} (Equivalence.reflexive (Setoid.eq fieldOfFractionsSetoid) {record { num = Ring.1R R ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I}}) (simpPower n)) (transitive (transitive (transitive *Commutative (transitive identIsIdent (+WellDefined identIsIdent identIsIdent))) (symmetric identIsIdent)) (*WellDefined (symmetric identIsIdent) reflexive))

  lemma : (n : ℕ) {num denom : A} .(d!=0 : denom ∼ 0G → False) → (num * denom) < positiveEltPower additiveGroup 1R n → fieldOfFractionsComparison (record { num = num ; denom = denom ; denomNonzero = d!=0}) record { num = positiveEltPower additiveGroup (Ring.1R R) n ; denom = 1R ; denomNonzero = IntegralDomain.nontrivial I }
  lemma n {num} {denom} d!=0 numdenom<n with totality 0G denom
  ... | inl (inl 0<denom) with totality 0G 1R
  ... | inl (inl 0<1) = {!!}
  ... | inl (inr x) = exFalso (1<0False x)
  ... | inr x = exFalso (nonempty x)
  lemma n {num} {denom} d!=0 numdenom<n | inl (inr denom<0) with totality 0G 1R
  ... | inl (inl 0<1) = {!!}
  ... | inl (inr 1<0) = exFalso (1<0False 1<0)
  ... | inr 0=1 = exFalso (nonempty 0=1)
  lemma n {num} {denom} d!=0 numdenom<n | inr 0=denom = exFalso (d!=0 (symmetric 0=denom))

fieldOfFractionsArchimedean : Archimedean (toGroup R pRing) → ArchimedeanField {F = fieldOfFractions} record { oRing = fieldOfFractionsOrderedRing }
fieldOfFractionsArchimedean arch (record { num = num ; denom = denom ; denomNonzero = denom!=0 }) with arch (num * denom) {!!} {!!} {!!}
... | bl = {!!}
--... | N , pr = N , SetoidPartialOrder.<WellDefined fieldOfFractionsOrder {record { denomNonzero = denom!=0 }} {record { denomNonzero = denom!=0 }} {record { denomNonzero = λ t → nonempty (symmetric t) }} {record { denomNonzero = d (positiveEltPower fieldOfFractionsGroup record { num = 1R ; denom = 1R ; denomNonzero = λ t → nonempty (symmetric t) } N) }} (Equivalence.reflexive (Setoid.eq fieldOfFractionsSetoid) { record { denomNonzero = denom!=0 } }) (Equivalence.symmetric (Setoid.eq fieldOfFractionsSetoid) {record { denomNonzero = λ t → d (positiveEltPower fieldOfFractionsGroup record { num = 1R ; denom = 1R ; denomNonzero = λ t → nonempty (symmetric t) } N) t }} {record { denomNonzero = λ t → nonempty (symmetric t) }} (simpPower N)) (lemma N denom!=0 pr)
