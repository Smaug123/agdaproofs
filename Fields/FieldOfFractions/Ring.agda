{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Rings.Lemmas
open import Rings.IntegralDomains
open import Fields.Fields
open import Functions
open import Setoids.Setoids
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.FieldOfFractions.Ring {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Setoid I
open import Fields.FieldOfFractions.Addition I
open import Fields.FieldOfFractions.Group I
open import Fields.FieldOfFractions.Multiplication I

fieldOfFractionsRing : Ring fieldOfFractionsSetoid fieldOfFractionsPlus fieldOfFractionsTimes
Ring.additiveGroup fieldOfFractionsRing = fieldOfFractionsGroup
Ring.*WellDefined fieldOfFractionsRing {a} {b} {c} {d} = fieldOfFractionsTimesWellDefined {a} {b} {c} {d}
Ring.1R fieldOfFractionsRing = Ring.1R R ,, (Ring.1R R , IntegralDomain.nontrivial I)
Ring.groupIsAbelian fieldOfFractionsRing {a ,, (b , _)} {c ,, (d , _)} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((a * d) + (b * c)) * (d * b)) ∼ ((b * d) * ((c * b) + (d * a)))
    need = transitive (Ring.*Commutative R) (Ring.*WellDefined R (Ring.*Commutative R) (transitive (Group.+WellDefined (Ring.additiveGroup R) (Ring.*Commutative R) (Ring.*Commutative R)) (Ring.groupIsAbelian R)))
Ring.*Associative fieldOfFractionsRing {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} = need
  where
    open Setoid S
    open Equivalence eq
    need : ((a * (c * e)) * ((b * d) * f)) ∼ ((b * (d * f)) * ((a * c) * e))
    need = transitive (Ring.*WellDefined R (Ring.*Associative R) (symmetric (Ring.*Associative R))) (Ring.*Commutative R)
Ring.*Commutative fieldOfFractionsRing {a ,, (b , _)} {c ,, (d , _)} = need
  where
    open Setoid S
    open Equivalence eq
    need : ((a * c) * (d * b)) ∼ ((b * d) * (c * a))
    need = transitive (Ring.*Commutative R) (Ring.*WellDefined R (Ring.*Commutative R) (Ring.*Commutative R))
Ring.*DistributesOver+ fieldOfFractionsRing {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} = need
  where
    open Setoid S
    open Ring R
    open Equivalence eq
    inter : b * (a * ((c * f) + (d * e))) ∼ (((a * c) * (b * f)) + ((b * d) * (a * e)))
    inter = transitive *Associative (transitive *DistributesOver+ (Group.+WellDefined additiveGroup (transitive *Associative (transitive (*WellDefined (transitive (*WellDefined (*Commutative) reflexive) (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative))) reflexive) (symmetric *Associative))) (transitive *Associative (transitive (*WellDefined (transitive (symmetric *Associative) (transitive (*WellDefined reflexive *Commutative) *Associative)) reflexive) (symmetric *Associative)))))
    need : ((a * ((c * f) + (d * e))) * ((b * d) * (b * f))) ∼ ((b * (d * f)) * (((a * c) * (b * f)) + ((b * d) * (a * e))))
    need = transitive (Ring.*WellDefined R reflexive (Ring.*WellDefined R reflexive (Ring.*Commutative R))) (transitive (Ring.*WellDefined R reflexive (Ring.*Associative R)) (transitive (Ring.*Commutative R) (transitive (Ring.*WellDefined R (Ring.*WellDefined R (symmetric (Ring.*Associative R)) reflexive) reflexive) (transitive (symmetric (Ring.*Associative R)) (Ring.*WellDefined R reflexive inter)))))
Ring.identIsIdent fieldOfFractionsRing {a ,, (b , _)} = need
  where
    open Setoid S
    open Equivalence eq
    need : (((Ring.1R R) * a) * b) ∼ (((Ring.1R R * b)) * a)
    need = transitive (Ring.*WellDefined R (Ring.identIsIdent R) reflexive) (transitive (Ring.*Commutative R) (Ring.*WellDefined R (symmetric (Ring.identIsIdent R)) reflexive))