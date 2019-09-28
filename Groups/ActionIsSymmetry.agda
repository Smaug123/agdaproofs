{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Groups.Lemmas
open import Groups.Groups
open import Groups.SymmetryGroups
open import Groups.Groups2
open import Groups.Actions

module Groups.ActionIsSymmetry where

actionPermutation : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} → (action : GroupAction G T) → (g : A) → SymmetryGroupElements T
actionPermutation {B = B} {T = T} {_+_ = _+_} {G = G} action g = sym {f = λ x → (GroupAction.action action g x)} (record { inj = record { injective = inj ; wellDefined = GroupAction.actionWellDefined2 action } ; surj = record { surjective = surj ; wellDefined = GroupAction.actionWellDefined2 action } })
  where
    open Setoid T
    open Reflexive (Equivalence.reflexiveEq (Setoid.eq T))
    open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
    open Transitive (Equivalence.transitiveEq (Setoid.eq T))
    open Group G
    inj : {x y : B} → (Setoid._∼_ T (GroupAction.action action g x) (GroupAction.action action g y)) → Setoid._∼_ T x y
    inj {x} {y} gx=gy = transitive (symmetric (GroupAction.identityAction action)) (transitive (transitive (symmetric (GroupAction.actionWellDefined1 action (invLeft {g}))) (transitive (transitive (GroupAction.associativeAction action) (transitive (GroupAction.actionWellDefined2 action gx=gy) (symmetric (GroupAction.associativeAction action)))) (GroupAction.actionWellDefined1 action (invLeft {g})))) (GroupAction.identityAction action))
    surj : {x : B} → Sg B (λ a → GroupAction.action action g a ∼ x)
    surj {x} = GroupAction.action action (inverse g) x , transitive (symmetric (GroupAction.associativeAction action)) (transitive (GroupAction.actionWellDefined1 action invRight) (GroupAction.identityAction action))

actionPermutationMapIsHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) → GroupHom G (symmetricGroup T) (actionPermutation action)
GroupHom.groupHom (actionPermutationMapIsHom {T = T} action) = ExtensionallyEqual.eq λ {z} → GroupAction.associativeAction action
  where
    open Setoid T
    open Reflexive (Equivalence.reflexiveEq (Setoid.eq T))
    open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
    open Transitive (Equivalence.transitiveEq (Setoid.eq T))
GroupHom.wellDefined (actionPermutationMapIsHom action) x=y = ExtensionallyEqual.eq λ {z} → GroupAction.actionWellDefined1 action x=y
