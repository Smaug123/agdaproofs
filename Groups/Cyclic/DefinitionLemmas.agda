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
open import Groups.Lemmas
open import Groups.Subgroups.Definition
open import Groups.Abelian.Definition
open import Groups.Definition
open import Groups.Cyclic.Definition
open import Semirings.Definition

module Groups.Cyclic.DefinitionLemmas {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} (G : Group S _+_) where

open Setoid S
open Group G
open Equivalence eq

elementPowerCommutes : (x : A) (n : ℕ) → (x + positiveEltPower G x n) ∼ ((positiveEltPower G x n) + x)
elementPowerCommutes x zero = transitive identRight (symmetric identLeft)
elementPowerCommutes x (succ n) = transitive (+WellDefined reflexive (elementPowerCommutes x n)) +Associative

elementPowerCollapse : (x : A) (i j : ℤ) → Setoid._∼_ S ((elementPower G x i) + (elementPower G x j)) (elementPower G x (i +Z j))
elementPowerCollapse x (nonneg a) (nonneg b) rewrite equalityCommutative (+Zinherits a b) = positiveEltPowerCollapse G x a b
elementPowerCollapse x (nonneg zero) (negSucc b) = identLeft
elementPowerCollapse x (nonneg (succ a)) (negSucc zero) = transitive (+WellDefined (elementPowerCommutes x a) reflexive) (transitive (symmetric +Associative) (transitive (+WellDefined reflexive (transitive (+WellDefined reflexive (invContravariant G)) (transitive (+WellDefined reflexive (transitive (+WellDefined (invIdent G) reflexive) identLeft)) invRight))) identRight))
elementPowerCollapse x (nonneg (succ a)) (negSucc (succ b)) = transitive (transitive (+WellDefined (elementPowerCommutes x a) reflexive) (transitive (symmetric +Associative) (+WellDefined reflexive (transitive (transitive (+WellDefined reflexive (inverseWellDefined G (transitive (+WellDefined reflexive (elementPowerCommutes x b)) +Associative))) (transitive (+WellDefined reflexive (invContravariant G)) (transitive +Associative (transitive (+WellDefined invRight (invContravariant G)) identLeft)))) (symmetric (invContravariant G)))))) (elementPowerCollapse x (nonneg a) (negSucc b))
elementPowerCollapse x (negSucc zero) (nonneg zero) = identRight
elementPowerCollapse x (negSucc zero) (nonneg (succ b)) = transitive (transitive +Associative (+WellDefined (transitive (+WellDefined (inverseWellDefined G identRight) reflexive) invLeft) reflexive)) identLeft
elementPowerCollapse x (negSucc (succ a)) (nonneg zero) = identRight
elementPowerCollapse x (negSucc (succ a)) (nonneg (succ b)) = transitive (transitive +Associative (+WellDefined (transitive (+WellDefined (invContravariant G) reflexive) (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight))) reflexive)) (elementPowerCollapse x (negSucc a) (nonneg b))
elementPowerCollapse x (negSucc a) (negSucc b) = transitive (+WellDefined reflexive (invContravariant G)) (transitive (transitive (transitive +Associative (+WellDefined (transitive (symmetric (invContravariant G)) (transitive (inverseWellDefined G +Associative) (transitive (inverseWellDefined G (+WellDefined (symmetric (elementPowerCommutes x b)) reflexive)) (transitive (inverseWellDefined G (symmetric +Associative)) (transitive (invContravariant G) (+WellDefined (inverseWellDefined G (transitive (positiveEltPowerCollapse G x b a) (identityOfIndiscernablesRight _∼_ reflexive (applyEquality (positiveEltPower G x) {b +N a} {a +N b} (Semiring.commutative ℕSemiring b a))))) reflexive)))))) reflexive)) (+WellDefined (symmetric (invContravariant G)) reflexive)) (symmetric (invContravariant G)))

