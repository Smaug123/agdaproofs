{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions.Definition

module Orders.Partial.Definition {a : _} (carrier : Set a) where

record PartialOrder {b : _} : Set (a ⊔ lsuc b) where
  field
    _<_ : Rel {a} {b} carrier
    irreflexive : {x : carrier} → (x < x) → False
    <Transitive : {a b c : carrier} → (a < b) → (b < c) → (a < c)
  <WellDefined : {r s t u : carrier} → (r ≡ t) → (s ≡ u) → r < s → t < u
  <WellDefined refl refl r<s = r<s
