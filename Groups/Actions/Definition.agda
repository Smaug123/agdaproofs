{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Groups.Definition
open import Groups.Lemmas
open import Groups.Groups
open import Sets.EquivalenceRelations

module Groups.Actions.Definition where

record GroupAction {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·_ : A → A → A} {B : Set n} (G : Group S _·_) (X : Setoid {n} {p} B) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Group G
  open Setoid S renaming (_∼_ to _∼G_)
  open Setoid X renaming (_∼_ to _∼X_)
  field
    action : A → B → B
    actionWellDefined1 : {g h : A} → {x : B} → (g ∼G h) → action g x ∼X action h x
    actionWellDefined2 : {g : A} → {x y : B} → (x ∼X y) → action g x ∼X action g y
    identityAction : {x : B} → action 0G x ∼X x
    associativeAction : {x : B} → {g h : A} → action (g · h) x ∼X action g (action h x)
