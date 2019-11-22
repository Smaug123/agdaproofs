{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Rings.Subrings.Definition
open import Rings.Isomorphisms.Definition
open import Groups.Isomorphisms.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.Ideals.FirstIsomorphismTheorem {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_+A_ _*A_ : A → A → A} {_+B_ _*B_ : B → B → B} {R1 : Ring S _+A_ _*A_} {R2 : Ring T _+B_ _*B_} {f : A → B} (hom : RingHom R1 R2 f) where

open import Rings.Quotients.Definition R1 R2 hom
open import Rings.Homomorphisms.Image hom
open Setoid T
open Equivalence eq
open import Groups.FirstIsomorphismTheorem (RingHom.groupHom hom)

ringFirstIsomorphismTheorem' : RingsIsomorphic quotientByRingHom (subringIsRing R2 imageGroupSubring)
RingsIsomorphic.f ringFirstIsomorphismTheorem' a = f a , (a , reflexive)
RingHom.preserves1 (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem')) = RingHom.preserves1 hom
RingHom.ringHom (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem')) {r} {s} = RingHom.ringHom hom
RingHom.groupHom (RingIso.ringHom (RingsIsomorphic.iso ringFirstIsomorphismTheorem')) = GroupIso.groupHom (GroupsIsomorphic.proof (groupFirstIsomorphismTheorem'))
RingIso.bijective (RingsIsomorphic.iso ringFirstIsomorphismTheorem') = GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem')
