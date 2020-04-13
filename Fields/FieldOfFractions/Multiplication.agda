{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations


module Fields.FieldOfFractions.Multiplication {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Setoid I

fieldOfFractionsTimes : fieldOfFractionsSet → fieldOfFractionsSet → fieldOfFractionsSet
fieldOfFractionsTimes (record { num = a ; denom = b ; denomNonzero = b!=0 }) (record { num = c ; denom = d ; denomNonzero = d!=0 }) = record { num = a * c ; denom = b * d ; denomNonzero = ans }
  where
    open Setoid S
    open Ring R
    ans : ((b * d) ∼ Ring.0R R) → False
    ans pr with IntegralDomain.intDom I pr
    ans pr | f = exFalso (d!=0 (f b!=0))

fieldOfFractionsTimesWellDefined : {a b c d : fieldOfFractionsSet} → (Setoid._∼_ fieldOfFractionsSetoid a c) → (Setoid._∼_ fieldOfFractionsSetoid b d) → (Setoid._∼_ fieldOfFractionsSetoid (fieldOfFractionsTimes a b) (fieldOfFractionsTimes c d))
fieldOfFractionsTimesWellDefined {record { num = a ; denom = b }} {record { num = c ; denom = d }} {record { num = e ; denom = f }} {record { num = g ; denom = h }} af=be ch=dg = need
  where
    open Setoid S
    open Equivalence eq
    need : ((a * c) * (f * h)) ∼ ((b * d) * (e * g))
    need = transitive (Ring.*WellDefined R reflexive (Ring.*Commutative R)) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (symmetric (Ring.*Associative R)) reflexive) (transitive (Ring.*WellDefined R (Ring.*WellDefined R reflexive ch=dg) reflexive) (transitive (Ring.*Commutative R) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (Ring.*Commutative R) reflexive) (transitive (Ring.*WellDefined R af=be reflexive) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (transitive (symmetric (Ring.*Associative R)) (transitive (Ring.*WellDefined R reflexive (Ring.*Commutative R)) (Ring.*Associative R))) reflexive) (symmetric (Ring.*Associative R)))))))))))
