{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Groups.Lemmas
open import Groups.Homomorphisms.Definition
open import Groups.Groups
open import Groups.SymmetricGroups.Definition
open import Groups.Groups2
open import Groups.Actions.Definition
open import Sets.EquivalenceRelations

module Groups.ActionIsSymmetry {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (gAction : GroupAction G T) where

open Group G
open GroupAction gAction

actionPermutation : (g : A) → SymmetryGroupElements T
actionPermutation g = sym {f = λ x → action g x} (record { inj = record { injective = inj ; wellDefined = actionWellDefined2 } ; surj = record { surjective = surj ; wellDefined = actionWellDefined2 } })
  where
    open Setoid T
    open Equivalence eq
    inj : {x y : B} → (Setoid._∼_ T (action g x) (action g y)) → Setoid._∼_ T x y
    inj {x} {y} gx=gy = transitive (symmetric identityAction) (transitive (transitive (symmetric (actionWellDefined1 (invLeft {g}))) (transitive (transitive associativeAction (transitive (actionWellDefined2 gx=gy) (symmetric associativeAction))) (actionWellDefined1 (invLeft {g})))) identityAction)
    surj : {x : B} → Sg B (λ a → action g a ∼ x)
    surj {x} = action (inverse g) x , transitive (symmetric associativeAction) (transitive (actionWellDefined1 invRight) identityAction)

actionPermutationMapIsHom : GroupHom G (symmetricGroup T) actionPermutation
GroupHom.groupHom actionPermutationMapIsHom = associativeAction
GroupHom.wellDefined actionPermutationMapIsHom x=y = actionWellDefined1 x=y
