{-# OPTIONS --warning=error --safe --without-K #-}

open import Functions
open import Sets.FinSet
open import LogicalFormulae
open import Groups.Definition
open import Groups.Groups
open import Groups.FiniteGroups.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Abelian.Definition
open import Setoids.Setoids
open import Fields.FieldOfFractions.Setoid
open import Sets.EquivalenceRelations
open import Groups.Lemmas
open import Groups.QuotientGroup.Definition

module Groups.QuotientGroup.Lemmas {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} (G : Group S _+A_) (H : Group T _+B_) {f : A → B} (fHom : GroupHom G H f) where

projectionMapIsGroupHom : GroupHom G (quotientGroupByHom G fHom) id
GroupHom.groupHom projectionMapIsGroupHom {x} {y} = quotientGroupLemma G fHom (Equivalence.reflexive (Setoid.eq T))
GroupHom.wellDefined projectionMapIsGroupHom x=y = quotientGroupLemma G fHom (GroupHom.wellDefined fHom x=y)
