{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Integers
open import Numbers.Integers.Addition
open import Sets.FinSet
open import Groups.Homomorphisms.Definition
open import Groups.Groups
open import Groups.Subgroups.Definition
open import Groups.Abelian.Definition
open import Groups.Definition

module Groups.Cyclic.Definition {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) where

open Setoid S
open Group G
open Equivalence eq

positiveEltPower : (x : A) (i : ℕ) → A
positiveEltPower x 0 = Group.0G G
positiveEltPower x (succ i) = x · (positiveEltPower x i)

positiveEltPowerCollapse : (x : A) (i j : ℕ) → Setoid._∼_ S ((positiveEltPower x i) · (positiveEltPower x j)) (positiveEltPower x (i +N j))
positiveEltPowerCollapse x zero j = Group.identLeft G
positiveEltPowerCollapse x (succ i) j = transitive (symmetric +Associative) (+WellDefined reflexive (positiveEltPowerCollapse x i j))

elementPower : (x : A) (i : ℤ) → A
elementPower x (nonneg i) = positiveEltPower x i
elementPower x (negSucc i) = Group.inverse G (positiveEltPower x (succ i))

record CyclicGroup : Set (m ⊔ n) where
  field
    generator : A
    cyclic : {a : A} → (Sg ℤ (λ i → Setoid._∼_ S (elementPower generator i) a))
