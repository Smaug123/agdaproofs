{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Rings.Subrings.Definition
open import Rings.Cosets
open import Rings.Isomorphisms.Definition
open import Groups.Isomorphisms.Definition


module Rings.Ideals.FirstIsomorphismTheorem {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_+A_ _*A_ : A → A → A} {_+B_ _*B_ : B → B → B} {R1 : Ring S _+A_ _*A_} {R2 : Ring T _+B_ _*B_} {f : A → B} (hom : RingHom R1 R2 f) where

open import Rings.Quotients.Definition R1 R2 hom
open import Rings.Homomorphisms.Image hom
open import Rings.Homomorphisms.Kernel hom
open Setoid T
open Equivalence eq
open import Groups.FirstIsomorphismTheorem (RingHom.groupHom hom)

ringFirstIsomorphismTheorem : RingsIsomorphic (cosetRing R1 ringKernelIsIdeal) (subringIsRing R2 imageGroupSubring)
RingsIsomorphic.f ringFirstIsomorphismTheorem = GroupsIsomorphic.isomorphism groupFirstIsomorphismTheorem
RingHom.preserves1 (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem)) = RingHom.preserves1 hom
RingHom.ringHom (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem)) = RingHom.ringHom hom
GroupHom.groupHom (RingHom.groupHom (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem))) = GroupHom.groupHom (RingHom.groupHom hom)
GroupHom.wellDefined (RingHom.groupHom (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem))) {x} {y} x=y = transferToRight (Ring.additiveGroup R2) t
  where
    t : f x +B Group.inverse (Ring.additiveGroup R2) (f y) ∼ Ring.0R R2
    t = transitive (Ring.groupIsAbelian R2) (transitive (Group.+WellDefined (Ring.additiveGroup R2) (symmetric (homRespectsInverse (RingHom.groupHom hom))) reflexive) (transitive (symmetric (GroupHom.groupHom (RingHom.groupHom hom))) x=y))
RingIso.bijective (RingsIsomorphic.iso ringFirstIsomorphismTheorem) = GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem)

ringFirstIsomorphismTheorem' : RingsIsomorphic quotientByRingHom (subringIsRing R2 imageGroupSubring)
RingsIsomorphic.f ringFirstIsomorphismTheorem' a = f a , (a , reflexive)
RingHom.preserves1 (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem')) = RingHom.preserves1 hom
RingHom.ringHom (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem')) {r} {s} = RingHom.ringHom hom
RingHom.groupHom (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem')) = GroupIso.groupHom (GroupsIsomorphic.proof (groupFirstIsomorphismTheorem'))
RingIso.bijective (RingsIsomorphic.iso ringFirstIsomorphismTheorem') = GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem')
