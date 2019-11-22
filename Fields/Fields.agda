{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Rings.Definition
open import Rings.Lemmas
open import Setoids.Setoids
open import Setoids.Orders
open import Orders
open import Rings.IntegralDomains.Definition
open import Functions
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Fields where

record Field {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) : Set (lsuc m ⊔ n) where
  open Ring R
  open Group additiveGroup
  open Setoid S
  field
    allInvertible : (a : A) → ((a ∼ Group.0G (Ring.additiveGroup R)) → False) → Sg A (λ t → t * a ∼ 1R)
    nontrivial : (0R ∼ 1R) → False
  0F : A
  0F = Ring.0R R

record Field' {m n : _} : Set (lsuc m ⊔ lsuc n) where
  field
    A : Set m
    S : Setoid {m} {n} A
    _+_ : A → A → A
    _*_ : A → A → A
    R : Ring S _+_ _*_
    isField : Field R

encapsulateField : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) → Field'
encapsulateField {A = A} {S = S} {_+_} {_*_} {R} F = record { A = A ; S = S ; _+_ = _+_ ; _*_ = _*_ ; R = R ; isField = F }


{-
record OrderedField {n} {A : Set n} {R : Ring A} (F : Field R) : Set (lsuc n) where
  open Field F
  field
    ord : TotalOrder A
  open TotalOrder ord
  open Ring R
  field
    productPos : {a b : A} → (0R < a) → (0R < b) → (0R < (a * b))
    orderRespectsAddition : {a b c : A} → (a < b) → (a + c) < (b + c)

-}
