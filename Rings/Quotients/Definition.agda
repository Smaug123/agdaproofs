{-# OPTIONS --warning=error --safe --without-K #-}

open import Functions
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Definition
open import Setoids.Setoids
open import Rings.Definition
open import Sets.EquivalenceRelations
open import Groups.QuotientGroup.Definition

module Rings.Quotients.Definition {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ _*A_ : A → A → A} {_+B_ _*B_ : B → B → B} (R : Ring S _+A_ _*A_) (R2 : Ring T _+B_ _*B_) {underf : A → B} (f : RingHom R R2 underf) where

open import Groups.QuotientGroup.Lemmas (Ring.additiveGroup R) (Ring.additiveGroup R2) (RingHom.groupHom f)

quotientByRingHom : Ring (quotientGroupSetoid (Ring.additiveGroup R) (RingHom.groupHom f)) _+A_ _*A_
Ring.additiveGroup quotientByRingHom = quotientGroupByHom (Ring.additiveGroup R) (RingHom.groupHom f)
Ring.*WellDefined quotientByRingHom fr=ft fs=fu = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (transitive (RingHom.ringHom f) (transitive (Ring.*WellDefined R2 (quotientGroupLemma' (Ring.additiveGroup R) (RingHom.groupHom f) fr=ft) (quotientGroupLemma' (Ring.additiveGroup R) (RingHom.groupHom f) fs=fu)) (symmetric (RingHom.ringHom f))))
  where
    open Setoid T
    open Equivalence eq
Ring.1R quotientByRingHom = Ring.1R R
Ring.groupIsAbelian quotientByRingHom = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (GroupHom.wellDefined (RingHom.groupHom f) (Ring.groupIsAbelian R))
Ring.*Associative quotientByRingHom = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (GroupHom.wellDefined (RingHom.groupHom f) (Ring.*Associative R))
Ring.*Commutative quotientByRingHom = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (GroupHom.wellDefined (RingHom.groupHom f) (Ring.*Commutative R))
Ring.*DistributesOver+ quotientByRingHom = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (GroupHom.wellDefined (RingHom.groupHom f) (Ring.*DistributesOver+ R))
Ring.identIsIdent quotientByRingHom = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (GroupHom.wellDefined (RingHom.groupHom f) (Ring.identIsIdent R))

projectionMapIsHom : RingHom R quotientByRingHom id
RingHom.preserves1 projectionMapIsHom = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (Equivalence.reflexive (Setoid.eq T))
RingHom.ringHom projectionMapIsHom = quotientGroupLemma (Ring.additiveGroup R) (RingHom.groupHom f) (Equivalence.reflexive (Setoid.eq T))
RingHom.groupHom projectionMapIsHom = projectionMapIsGroupHom
