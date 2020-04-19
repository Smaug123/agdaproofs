{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Rings.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.IntegralDomains.Definition
open import Rings.IntegralDomains.Lemmas

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.FieldOfFractions.Setoid {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

record fieldOfFractionsSet : Set (a ⊔ b) where
  field
    num : A
    denom : A
    .denomNonzero : (Setoid._∼_ S denom (Ring.0R R) → False)

fieldOfFractionsSetoid : Setoid fieldOfFractionsSet
Setoid._∼_ fieldOfFractionsSetoid (record { num = a ; denom = b ; denomNonzero = b!=0 }) (record { num = c ; denom = d ; denomNonzero = d!=0 }) = Setoid._∼_ S (a * d) (b * c)
Equivalence.reflexive (Setoid.eq fieldOfFractionsSetoid) {record { num = a ; denom = b ; denomNonzero = b!=0 }} = Ring.*Commutative R
Equivalence.symmetric (Setoid.eq fieldOfFractionsSetoid) {record { num = a ; denom = b ; denomNonzero = b!=0 }} {record { num = c ; denom = d ; denomNonzero = d!=0 }} ad=bc = transitive (Ring.*Commutative R) (transitive (symmetric ad=bc) (Ring.*Commutative R))
  where
    open Equivalence (Setoid.eq S)
Equivalence.transitive (Setoid.eq fieldOfFractionsSetoid) {record { num = a ; denom = b ; denomNonzero = b!=0 }} {record { num = c ; denom = d ; denomNonzero = d!=0 }} {record { num = e ; denom = f ; denomNonzero = f!=0 }} ad=bc cf=de = p5
  where
    open Setoid S
    open Ring R
    open Equivalence eq
    p : (a * d) * f ∼ (b * c) * f
    p = Ring.*WellDefined R ad=bc reflexive
    p2 : (a * f) * d ∼ b * (d * e)
    p2 = transitive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) (transitive p (transitive (symmetric *Associative) (*WellDefined reflexive cf=de)))
    p3 : (a * f) * d ∼ (b * e) * d
    p3 = transitive p2 (transitive (*WellDefined reflexive *Commutative) *Associative)
    p4 : ((d ∼ 0R) → False) → ((a * f) ∼ (b * e))
    p4 = cancelIntDom I (transitive *Commutative (transitive p3 *Commutative))
    p5 : (a * f) ∼ (b * e)
    p5 = p4 λ t → exFalso (d!=0 t)
