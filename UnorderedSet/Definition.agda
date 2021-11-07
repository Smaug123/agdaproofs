{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Decidable.Sets
open import Lists.Lists
open import Numbers.Naturals.Semiring

module UnorderedSet.Definition {a : _} {V : Set a} (dec : DecidableSet V) where

data UnorderedSetOf : List V → Set a where
  empty' : UnorderedSetOf []
  addCons : (v : V) → (vs : List V) → .(contains vs v → False) → UnorderedSetOf vs → UnorderedSetOf (v :: vs)

record UnorderedSet : Set a where
  field
    elts : List V
    set : UnorderedSetOf elts

empty : UnorderedSet
empty = record { elts = [] ; set = empty' }

add : V → UnorderedSet → UnorderedSet
add v record { elts = elts ; set = set } with containsDecidable dec elts v
... | inl x = record { elts = elts ; set = set }
... | inr x = record { elts = v :: elts ; set = addCons v elts x set }

singleton : V → UnorderedSet
singleton v = record { elts = v :: [] ; set = addCons v [] (λ ()) empty' }

ofList : (l : List V) → UnorderedSet
ofList [] = record { elts = [] ; set = empty' }
ofList (x :: l) = add x (ofList l)

union : UnorderedSet → UnorderedSet → UnorderedSet
union record { elts = eltsA ; set = setA } record { elts = eltsB ; set = setB } = ofList (eltsA ++ eltsB)

count : UnorderedSet → ℕ
count record { elts = e ; set = _ } = length e

setContains : (v : V) → UnorderedSet → Set a
setContains v record { elts = elts ; set = set } = contains elts v
