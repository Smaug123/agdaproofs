{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Orders
open import Maybe
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import KeyValue
open import Vectors

open import Naturals

module KeyValueWithDomain where

  record MapWithDomain {a b c : _} (keyDom : Set a) (values : Set b) (keyOrder : TotalOrder {_} {c} keyDom) : Set (a ⊔ b ⊔ c) where
    field
      map : Map keyDom values keyOrder
      domain : Vec keyDom (count map)
      domainIsIt : keys map ≡ domain
    lookup' : (key : keyDom) → (vecContains domain key) → Sg values (λ v → lookup map key ≡ yes v)
    lookup' k cont rewrite equalityCommutative domainIsIt = lookupCertain {keyOrder = keyOrder} map k cont
