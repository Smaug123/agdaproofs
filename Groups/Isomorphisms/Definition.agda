{-# OPTIONS --safe --warning=error --without-K #-}

open import Setoids.Setoids
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Groups.Definition
open import Groups.Homomorphisms.Definition

module Groups.Isomorphisms.Definition where

record GroupIso {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) (f : A → B) : Set (m ⊔ n ⊔ o ⊔ p) where
  open Setoid S renaming (_∼_ to _∼G_)
  open Setoid T renaming (_∼_ to _∼H_)
  field
    groupHom : GroupHom G H f
    bij : SetoidBijection S T f

record GroupsIsomorphic {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) : Set (m ⊔ n ⊔ o ⊔ p) where
  field
    isomorphism : A → B
    proof : GroupIso G H isomorphism
