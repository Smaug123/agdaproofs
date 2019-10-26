{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Orders
open import Setoids.Setoids
open import Functions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Setoids.Orders where

record SetoidPartialOrder {a b c : _} {A : Set a} (S : Setoid {a} {b} A) (_<_ : Rel {a} {c} A) : Set (a ⊔ b ⊔ c) where
  open Setoid S
  field
    <WellDefined : {a b c d : A} → (a ∼ b) → (c ∼ d) → a < c → b < d
    irreflexive : {x : A} → (x < x) → False
    transitive : {a b c : A} → (a < b) → (b < c) → (a < c)

record SetoidTotalOrder {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} (P : SetoidPartialOrder S _<_) : Set (a ⊔ b ⊔ c) where
  open Setoid S
  field
    totality : (a b : A) → ((a < b) || (b < a)) || (a ∼ b)
  partial : SetoidPartialOrder S _<_
  partial = P
  min : A → A → A
  min a b with totality a b
  min a b | inl (inl a<b) = a
  min a b | inl (inr b<a) = b
  min a b | inr a=b = a
  max : A → A → A
  max a b with totality a b
  max a b | inl (inl a<b) = b
  max a b | inl (inr b<a) = a
  max a b | inr a=b = b

partialOrderToSetoidPartialOrder : {a b : _} {A : Set a} (P : PartialOrder {a} {b} A) → SetoidPartialOrder (reflSetoid A) (PartialOrder._<_ P)
SetoidPartialOrder.<WellDefined (partialOrderToSetoidPartialOrder P) a=b c=d a<c rewrite a=b | c=d = a<c
SetoidPartialOrder.irreflexive (partialOrderToSetoidPartialOrder P) = PartialOrder.irreflexive P
SetoidPartialOrder.transitive (partialOrderToSetoidPartialOrder P) = PartialOrder.transitive P

totalOrderToSetoidTotalOrder : {a b : _} {A : Set a} (T : TotalOrder {a} {b} A) → SetoidTotalOrder (partialOrderToSetoidPartialOrder (TotalOrder.order T))
SetoidTotalOrder.totality (totalOrderToSetoidTotalOrder T) = TotalOrder.totality T
