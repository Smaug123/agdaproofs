{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Groups.Groups

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
