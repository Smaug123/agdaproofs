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
open import Groups.Subgroups.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Actions.Definition
open import Sets.EquivalenceRelations
open import Groups.Actions.Definition

module Groups.Actions.Stabiliser {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (act : GroupAction G T) where

open GroupAction act
open Setoid T

stabiliserPred : (x : B) → (g : A) → Set d
stabiliserPred x g = (action g x) ∼ x

stabiliserWellDefined : (x : B) → {g h : A} → Setoid._∼_ S g h → (stabiliserPred x g) → stabiliserPred x h
stabiliserWellDefined x {g} {h} g=h gx=x = transitive (actionWellDefined1 (Equivalence.symmetric (Setoid.eq S) g=h)) gx=x
  where
    open Equivalence eq

open Setoid T
open Equivalence (Setoid.eq T)

stabiliserSubgroup : (x : B) → Subgroup G (stabiliserPred x)
Subgroup.isSubset (stabiliserSubgroup x) = stabiliserWellDefined x
Subgroup.closedUnderPlus (stabiliserSubgroup x) gx=x hx=x = transitive associativeAction (transitive (actionWellDefined2 hx=x) gx=x)
Subgroup.containsIdentity (stabiliserSubgroup x) = identityAction
Subgroup.closedUnderInverse (stabiliserSubgroup x) {g} gx=x = transitive (transitive (transitive (actionWellDefined2 (symmetric gx=x)) (symmetric associativeAction)) (actionWellDefined1 (invLeft {g}))) identityAction
  where
    open Group G
