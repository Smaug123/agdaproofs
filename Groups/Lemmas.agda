{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Groups.Groups
open import Groups.Definition
open import Sets.EquivalenceRelations

module Groups.Lemmas where
  invInv : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → Setoid._∼_ S (Group.inverse G (Group.inverse G x)) x
  invInv {S = S} G {x} = symmetric (transferToRight' G invRight)
    where
      open Setoid S
      open Group G
      open Equivalence eq

  invIdent : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → Setoid._∼_ S (Group.inverse G (Group.0G G)) (Group.0G G)
  invIdent {S = S} G = symmetric (transferToRight' G (Group.identLeft G))
    where
      open Setoid S
      open Group G
      open Equivalence eq

  swapInv : {a b : _} {A : Set a} {_+_ : A → A → A} {S : Setoid {a} {b} A} (G : Group S _+_) → {x y : A} → Setoid._∼_ S (Group.inverse G x) y → Setoid._∼_ S x (Group.inverse G y)
  swapInv {S = S} G {x} {y} -x=y = transitive (symmetric (invInv G)) (inverseWellDefined G -x=y)
    where
      open Setoid S
      open Group G
      open Equivalence eq

  identityIsUnique : {a b : _} → {A : Set a} → {S : Setoid {a} {b} A} → {_·_ : A → A → A} → (G : Group S _·_) → (e : A) → ((b : A) → (Setoid._∼_ S (b · e) b)) → (Setoid._∼_ S e (Group.0G G))
  identityIsUnique {S = S} {_·_} g thing fb = transitive (symmetric identLeft) (fb 0G)
    where
      open Group g renaming (inverse to _^-1)
      open Setoid S
      open Equivalence eq
