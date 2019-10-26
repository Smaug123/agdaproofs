{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Rings.Definition
open import Rings.Order
open import Rings.Lemmas
open import Setoids.Setoids
open import Setoids.Orders
open import Orders
open import Rings.IntegralDomains
open import Functions
open import Sets.EquivalenceRelations
open import Fields.Fields

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Fields.Orders.Definition {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (F : Field R) where

open Ring R
open import Fields.Lemmas F

record OrderedField {p} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} (order : SetoidTotalOrder pOrder) : Set (lsuc (m ⊔ n ⊔ p)) where
  field
    oRing : OrderedRing R order
