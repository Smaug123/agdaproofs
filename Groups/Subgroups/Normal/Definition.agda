{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Groups
open import Groups.Definition
open import Orders
open import Numbers.Integers.Integers
open import Setoids.Setoids
open import LogicalFormulae
open import Sets.FinSet
open import Functions
open import Sets.EquivalenceRelations
open import Numbers.Naturals.Naturals
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Isomorphisms.Definition
open import Groups.Subgroups.Definition
open import Groups.Lemmas
open import Groups.Abelian.Definition
open import Groups.QuotientGroup.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Subgroups.Normal.Definition where

record NormalSubgroup {a} {b} {c} {d} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) {f : B → A} (hom : GroupHom H G f) : Set (a ⊔ b ⊔ c ⊔ d) where
  open Setoid S
  field
    subgroup : Subgroup G H hom
    normal : {g : A} {h : B} → Sg B (λ fromH → (g ·A (f h)) ·A (Group.inverse G g) ∼ f fromH)
