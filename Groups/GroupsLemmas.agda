{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Groups.Groups
open import Groups.GroupDefinition

module Groups.GroupsLemmas where
  invInv : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → {x : A} → Setoid._∼_ S (Group.inverse G (Group.inverse G x)) x
  invInv {S = S} G {x} = symmetric (transferToRight' G invRight)
    where
      open Setoid S
      open Group G
      open Equivalence eq
      open Symmetric symmetricEq

  invIdent : {a b : _} → {A : Set a} → {_·_ : A → A → A} → {S : Setoid {a} {b} A} → (G : Group S _·_) → Setoid._∼_ S (Group.inverse G (Group.identity G)) (Group.identity G)
  invIdent {S = S} G = symmetric (transferToRight' G (Group.multIdentLeft G))
    where
      open Setoid S
      open Group G
      open Equivalence eq
      open Symmetric symmetricEq

  swapInv : {a b : _} {A : Set a} {_+_ : A → A → A} {S : Setoid {a} {b} A} (G : Group S _+_) → {x y : A} → Setoid._∼_ S (Group.inverse G x) y → Setoid._∼_ S x (Group.inverse G y)
  swapInv {S = S} G {x} {y} -x=y = transitive (symmetric (invInv G)) (inverseWellDefined G -x=y)
    where
      open Setoid S
      open Group G
      open Equivalence eq
      open Symmetric symmetricEq
      open Transitive transitiveEq
