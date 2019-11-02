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

module Fields.FieldOfFractions.Multiplication {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Setoid I

fieldOfFractionsTimes : fieldOfFractionsSet → fieldOfFractionsSet → fieldOfFractionsSet
fieldOfFractionsTimes (a ,, (b , b!=0)) (c ,, (d , d!=0)) = (a * c) ,, ((b * d) , ans)
  where
    open Setoid S
    open Ring R
    ans : ((b * d) ∼ Ring.0R R) → False
    ans pr with IntegralDomain.intDom I pr
    ans pr | inl x = b!=0 x
    ans pr | inr x = d!=0 x

fieldOfFractionsTimesWellDefined : {a b c d : fieldOfFractionsSet} → (Setoid._∼_ fieldOfFractionsSetoid a c) → (Setoid._∼_ fieldOfFractionsSetoid b d) → (Setoid._∼_ fieldOfFractionsSetoid (fieldOfFractionsTimes a b) (fieldOfFractionsTimes c d))
fieldOfFractionsTimesWellDefined {a ,, (b , _)} {c ,, (d , _)} {e ,, (f , _)} {g ,, (h , _)} af=be ch=dg = need
  where
    open Setoid S
    open Equivalence eq
    need : ((a * c) * (f * h)) ∼ ((b * d) * (e * g))
    need = transitive (Ring.*WellDefined R reflexive (Ring.*Commutative R)) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (symmetric (Ring.*Associative R)) reflexive) (transitive (Ring.*WellDefined R (Ring.*WellDefined R reflexive ch=dg) reflexive) (transitive (Ring.*Commutative R) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (Ring.*Commutative R) reflexive) (transitive (Ring.*WellDefined R af=be reflexive) (transitive (Ring.*Associative R) (transitive (Ring.*WellDefined R (transitive (symmetric (Ring.*Associative R)) (transitive (Ring.*WellDefined R reflexive (Ring.*Commutative R)) (Ring.*Associative R))) reflexive) (symmetric (Ring.*Associative R)))))))))))
