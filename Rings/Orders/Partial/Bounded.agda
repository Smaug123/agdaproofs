{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Setoids.Setoids
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders.Partial.Definition
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Groups.Definition

module Rings.Orders.Partial.Bounded {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} (pRing : PartiallyOrderedRing R pOrder) where

open Group (Ring.additiveGroup R)
open import Groups.Lemmas (Ring.additiveGroup R)
open Setoid S
open Equivalence eq
open SetoidPartialOrder pOrder

BoundedAbove : Sequence A → Set (m ⊔ o)
BoundedAbove x = Sg A (λ K → (n : ℕ) → index x n < K)

BoundedBelow : Sequence A → Set (m ⊔ o)
BoundedBelow x = Sg A (λ K → (n : ℕ) → K < index x n)

Bounded : Sequence A → Set (m ⊔ o)
Bounded x = Sg A (λ K → (n : ℕ) → ((Group.inverse (Ring.additiveGroup R) K) < index x n) && (index x n < K))

boundNonzero : {s : Sequence A} → (b : Bounded s) → underlying b ∼ 0G → False
boundNonzero {s} (a , b) isEq with b 0
... | bad1 ,, bad2 = irreflexive (<Transitive bad1 (<WellDefined reflexive (transitive isEq (symmetric (transitive (inverseWellDefined isEq) invIdent))) bad2))
