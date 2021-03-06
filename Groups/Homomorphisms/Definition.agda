{-# OPTIONS --safe --warning=error --without-K #-}

open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Groups.Definition

module Groups.Homomorphisms.Definition where

record GroupHom {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) (f : A → B) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Group H
  open Setoid T
  field
    groupHom : {x y : A} → f (x ·A y) ∼ (f x) ·B (f y)
    wellDefined : {x y : A} → Setoid._∼_ S x y → f x ∼ f y
  groupHom' : {x y : A} → (f x) ·B (f y) ∼ f (x ·A y)
  groupHom' = Equivalence.symmetric eq groupHom

record InjectiveGroupHom {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} {underf : A → B} (f : GroupHom G H underf) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Setoid S renaming (_∼_ to _∼A_)
  open Setoid T renaming (_∼_ to _∼B_)
  field
    injective : SetoidInjection S T underf
