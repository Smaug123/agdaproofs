{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Groups.FreeGroup.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Decidable.Sets
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Semirings.Definition
open import Functions
open import Groups.Isomorphisms.Definition
open import Groups.FreeGroup.Word
open import Groups.FreeGroup.Group
open import Groups.FreeGroup.UniversalProperty

module Groups.FreeGroup.Lemmas {a : _} {A : Set a} (decA : DecidableSet A) where

freeGroupNonAbelian : {!!}
freeGroupNonAbelian = {!!}

freeGroupFunctorWellDefined : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → Bijection f → GroupsIsomorphic (freeGroup decA) (freeGroup decB)
GroupsIsomorphic.isomorphism (freeGroupFunctorWellDefined decB {f} bij) = universalPropertyFunction decA (freeGroup decB) λ a → freeEmbedding decB (f a)
GroupIso.groupHom (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)) = universalPropertyHom decA (freeGroup decB) λ a → freeEmbedding decB (f a)
GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)) = {!!}

freeGroupFunctorInjective : {b : _} {B : Set b} (decB : DecidableSet B) → GroupsIsomorphic (freeGroup decA) (freeGroup decB) → Sg (A → B) (λ f → Bijection f)
freeGroupFunctorInjective decB iso = {!!}

everyGroupQuotientOfFreeGroup : {!!}
everyGroupQuotientOfFreeGroup = {!!}

everyFGGroupQuotientOfFGFreeGroup : {!!}
everyFGGroupQuotientOfFGFreeGroup = {!!}

freeGroupTorsionFree : {!!}
freeGroupTorsionFree = {!!}

freeGroupInfinite : {!!}
freeGroupInfinite = {!!}
