{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations

module Fields.FieldOfFractions.Ring {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Setoid I
open import Fields.FieldOfFractions.Addition I
open import Fields.FieldOfFractions.Group I
open import Fields.FieldOfFractions.Multiplication I

fieldOfFractionsRing : Ring fieldOfFractionsSetoid fieldOfFractionsPlus fieldOfFractionsTimes
Ring.additiveGroup fieldOfFractionsRing = fieldOfFractionsGroup
Ring.*WellDefined fieldOfFractionsRing {a} {b} {c} {d} = fieldOfFractionsTimesWellDefined {a} {b} {c} {d}
Ring.1R fieldOfFractionsRing = record { num = Ring.1R R ; denom = Ring.1R R ; denomNonzero = IntegralDomain.nontrivial I }
Ring.groupIsAbelian fieldOfFractionsRing {record { num = a ; denom = b }} {record { num = c ; denom = d }} = Equivalence.transitive (Setoid.eq S) (Ring.*Commutative R) (Ring.*WellDefined R (Ring.*Commutative R) (Equivalence.transitive (Setoid.eq S) (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Commutative R) (Ring.*Commutative R)) (Ring.groupIsAbelian R)))
Ring.*Associative fieldOfFractionsRing {record { num = a ; denom = b }} {record { num = c ; denom = d }} {record { num = e ; denom = f }} = Equivalence.transitive (Setoid.eq S) (Ring.*WellDefined R (Ring.*Associative R) (Ring.*Associative' R)) (Ring.*Commutative R)
Ring.*Commutative fieldOfFractionsRing {record { num = a ; denom = b }} {record { num = c ; denom = d }} = Equivalence.transitive (Setoid.eq S) (Ring.*Commutative R) (Ring.*WellDefined R (Ring.*Commutative R) (Ring.*Commutative R))
Ring.*DistributesOver+ fieldOfFractionsRing {record { num = a ; denom = b }} {record { num = c ; denom = d }} {record { num = e ; denom = f }} = need
  where
    open Setoid S
    open Ring R
    open Equivalence eq
    inter : b * (a * ((c * f) + (d * e))) ∼ (((a * c) * (b * f)) + ((b * d) * (a * e)))
    inter = transitive *Associative (transitive *DistributesOver+ (Group.+WellDefined additiveGroup (transitive *Associative (transitive (*WellDefined (transitive (*WellDefined (*Commutative) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative))) reflexive) (symmetric *Associative))) (transitive *Associative (transitive (*WellDefined (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) reflexive) (symmetric *Associative)))))
    need : ((a * ((c * f) + (d * e))) * ((b * d) * (b * f))) ∼ ((b * (d * f)) * (((a * c) * (b * f)) + ((b * d) * (a * e))))
    need = transitive (Ring.*WellDefined R reflexive (Ring.*WellDefined R reflexive (Ring.*Commutative R))) (transitive (Ring.*WellDefined R reflexive (Ring.*Associative R)) (transitive (Ring.*Commutative R) (transitive (Ring.*WellDefined R (Ring.*WellDefined R (symmetric (Ring.*Associative R)) reflexive) reflexive) (transitive (symmetric (Ring.*Associative R)) (Ring.*WellDefined R reflexive inter)))))
Ring.identIsIdent fieldOfFractionsRing {record { num = a ; denom = b }} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((Ring.1R R) * a) * b) ∼ (((Ring.1R R * b)) * a)
    need = transitive (Ring.*WellDefined R (Ring.identIsIdent R) reflexive) (transitive (Ring.*Commutative R) (Ring.*WellDefined R (symmetric (Ring.identIsIdent R)) reflexive))
