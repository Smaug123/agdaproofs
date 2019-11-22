{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Homomorphisms.Definition
open import Rings.IntegralDomains.Definition
open import Fields.Fields
open import Functions
open import Setoids.Setoids
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.FieldOfFractions.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) where

open import Fields.FieldOfFractions.Setoid I
open import Fields.FieldOfFractions.Addition I
open import Fields.FieldOfFractions.Multiplication I
open import Fields.FieldOfFractions.Ring I
open import Fields.FieldOfFractions.Field I

embedIntoFieldOfFractions : A → fieldOfFractionsSet
embedIntoFieldOfFractions a = a ,, (Ring.1R R , IntegralDomain.nontrivial I)

homIntoFieldOfFractions : RingHom R fieldOfFractionsRing embedIntoFieldOfFractions
RingHom.preserves1 homIntoFieldOfFractions = Equivalence.reflexive (Setoid.eq S)
RingHom.ringHom homIntoFieldOfFractions {a} {b} = Equivalence.transitive (Setoid.eq S) (Ring.*WellDefined R (Equivalence.reflexive (Setoid.eq S)) (Ring.identIsIdent R)) (Ring.*Commutative R)
GroupHom.groupHom (RingHom.groupHom homIntoFieldOfFractions) {x} {y} = need
  where
    open Setoid S
    open Equivalence eq
    need : ((x + y) * (Ring.1R R * Ring.1R R)) ∼ (Ring.1R R * ((x * Ring.1R R) + (Ring.1R R * y)))
    need = transitive (transitive (Ring.*WellDefined R reflexive (Ring.identIsIdent R)) (transitive (Ring.*Commutative R) (transitive (Ring.identIsIdent R) (Group.+WellDefined (Ring.additiveGroup R) (symmetric (transitive (Ring.*Commutative R) (Ring.identIsIdent R))) (symmetric (Ring.identIsIdent R)))))) (symmetric (Ring.identIsIdent R))
GroupHom.wellDefined (RingHom.groupHom homIntoFieldOfFractions) x=y = transitive (Ring.*Commutative R) (Ring.*WellDefined R reflexive x=y)
  where
    open Equivalence (Setoid.eq S)

homIntoFieldOfFractionsIsInj : SetoidInjection S fieldOfFractionsSetoid embedIntoFieldOfFractions
SetoidInjection.wellDefined homIntoFieldOfFractionsIsInj x=y = transitive (Ring.*Commutative R) (Ring.*WellDefined R reflexive x=y)
  where
    open Equivalence (Setoid.eq S)
SetoidInjection.injective homIntoFieldOfFractionsIsInj x~y = transitive (symmetric identIsIdent) (transitive *Commutative (transitive x~y identIsIdent))
  where
    open Ring R
    open Setoid S
    open Equivalence eq
