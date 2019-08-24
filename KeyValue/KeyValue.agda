{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Orders
open import Maybe
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Vectors

open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order

module KeyValue.KeyValue where
  record KeyValue {a b c : _} (keys : Set a) (values : Set b) (maps : Set c) : Set (a ⊔ b ⊔ c) where
    field
      tryFind : maps → keys → Maybe values
      add : (map : maps) → keys → values → maps
      empty : maps
      count : maps → ℕ
      lookupAfterAdd : (map : maps) → (k : keys) → (v : values) → tryFind (add map k v) k ≡ yes v
      lookupAfterAdd' : (map : maps) → (k1 : keys) → (v : values) → (k2 : keys) → (k1 ≡ k2) || (tryFind (add map k1 v) k2 ≡ tryFind map k2)
      countAfterAdd' : (map : maps) → (k : keys) → (v : values) → (tryFind map k ≡ no) → count (add map k v) ≡ succ (count map)
      countAfterAdd : (map : maps) → (k : keys) → (v1 v2 : values) → (tryFind map k ≡ yes v2) → count (add map k v1) ≡ count map
