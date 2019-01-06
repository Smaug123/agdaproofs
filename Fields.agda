{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Groups
open import Rings
open import Setoids
open import Orders
open import IntegralDomains
open import Functions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields where
  record Field {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) : Set (lsuc m ⊔ n) where
    open Ring R
    open Group additiveGroup
    open Setoid S
    field
      allInvertible : (a : A) → ((a ∼ Group.identity (Ring.additiveGroup R)) → False) → Sg A (λ t → t * a ∼ 1R)
      nontrivial : (0R ∼ 1R) → False

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
