{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions.Definition

module Orders.Total.Definition {a : _} (carrier : Set a) where

open import Orders.Partial.Definition carrier

record TotalOrder {b : _} : Set (a ⊔ lsuc b) where
  field
    order : PartialOrder {b}
  _<_ : Rel carrier
  _<_ = PartialOrder._<_ order
  _≤_ : Rel carrier
  _≤_ a b = (a < b) || (a ≡ b)
  field
    totality : (a b : carrier) → ((a < b) || (b < a)) || (a ≡ b)

  min : carrier → carrier → carrier
  min a b with totality a b
  min a b | inl (inl a<b) = a
  min a b | inl (inr b<a) = b
  min a b | inr a=b = a
  max : carrier → carrier → carrier
  max a b with totality a b
  max a b | inl (inl a<b) = b
  max a b | inl (inr b<a) = a
  max a b | inr a=b = b

  irreflexive = PartialOrder.irreflexive order
  <Transitive = PartialOrder.<Transitive order
  <WellDefined = PartialOrder.<WellDefined order

