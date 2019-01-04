{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Groups
open import Naturals
open import Orders
open import Setoids
open import Functions
open import Rings

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module IntegralDomains where
  record IntegralDomain {n m : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) : Set (lsuc m ⊔ n) where
    field
      intDom : {a b : A} → Setoid._∼_ S (a * b) (Ring.0R R) → (Setoid._∼_ S a (Ring.0R R)) || (Setoid._∼_ S b (Ring.0R R))
      nontrivial : Setoid._∼_ S (Ring.1R R) (Ring.0R R) → False
