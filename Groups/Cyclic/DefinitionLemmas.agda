{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Numbers.Naturals.Semiring
open import Numbers.Integers.Integers
open import Numbers.Integers.Addition
open import Groups.Lemmas
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

positiveEltPowerInverse : (m : ℕ) → (x : A) → (positiveEltPower G (inverse x) m) ∼ inverse (positiveEltPower G x m)
positiveEltPowerInverse zero x = symmetric (invIdent G)
positiveEltPowerInverse (succ m) x = transitive (+WellDefined reflexive (positiveEltPowerInverse m x)) (transitive (symmetric (invContravariant G)) (inverseWellDefined G (symmetric (elementPowerCommutes x m))))

positiveEltPowerMultiplies : (m n : ℕ) → (x : A) → (positiveEltPower G x (m *N n)) ∼ (positiveEltPower G (positiveEltPower G x n) m)
positiveEltPowerMultiplies zero n x = reflexive
positiveEltPowerMultiplies (succ m) n x = transitive (symmetric (positiveEltPowerCollapse G x n (m *N n))) (+WellDefined reflexive (positiveEltPowerMultiplies m n x))

powerZero : (m : ℕ) → positiveEltPower G 0G m ∼ 0G
powerZero zero = reflexive
powerZero (succ m) = transitive identLeft (powerZero m)

elementPowerMultiplies : (m n : ℤ) → (x : A) → (elementPower G x (m *Z n)) ∼ (elementPower G (elementPower G x n) m)
elementPowerMultiplies (nonneg m) (nonneg n) x = positiveEltPowerMultiplies m n x
elementPowerMultiplies (nonneg zero) (negSucc n) x = reflexive
elementPowerMultiplies (nonneg (succ m)) (negSucc n) x =  transitive (transitive (inverseWellDefined G (transitive (transitive (elementPowerWellDefinedZ' G (nonneg (succ (n +N m *N n) +N m)) (nonneg (m *N succ n +N succ n)) (applyEquality nonneg (transitivity (applyEquality succ (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring n (m *N n) m)) (applyEquality (n +N_) (transitivity (transitivity (Semiring.commutative ℕSemiring _ m) (applyEquality (m +N_) (multiplicationNIsCommutative m n))) (multiplicationNIsCommutative (succ n) m))))) (Semiring.commutative ℕSemiring (succ n) _))) {x}) (symmetric (positiveEltPowerCollapse G x (m *N succ n) (succ n)))) (+WellDefined (positiveEltPowerMultiplies m (succ n) x) reflexive))) (invContravariant G)) (+WellDefined reflexive (symmetric (positiveEltPowerInverse m (x + positiveEltPower G x n))))
elementPowerMultiplies (negSucc m) (nonneg zero) r = transitive (symmetric (invIdent G)) (inverseWellDefined G (transitive (symmetric identLeft) (+WellDefined reflexive (symmetric (powerZero m)))))
elementPowerMultiplies (negSucc m) (nonneg (succ n)) x = inverseWellDefined G (transitive (transitive (+WellDefined reflexive (transitive (elementPowerWellDefinedZ' G (nonneg ((m +N n *N m) +N n)) (nonneg (n +N m *N succ n)) (applyEquality nonneg (transitivity (Semiring.commutative ℕSemiring _ n) (applyEquality (n +N_) (multiplicationNIsCommutative _ m)))) {x}) (symmetric (positiveEltPowerCollapse G x n (m *N succ n))))) +Associative) (+WellDefined reflexive (positiveEltPowerMultiplies m (succ n) x)))
elementPowerMultiplies (negSucc m) (negSucc n) r = transitive (transitive (transitive (transitive (elementPowerWellDefinedZ' G (nonneg (succ m *N succ n)) (nonneg (m *N succ n +N succ n)) (applyEquality nonneg (Semiring.commutative ℕSemiring (succ n) _)) {r}) (symmetric (positiveEltPowerCollapse G r (m *N succ n) (succ n)))) (transitive (elementPowerCollapse r (nonneg (m *N succ n)) (nonneg (succ n))) (transitive (transitive (elementPowerWellDefinedZ' G (nonneg (m *N succ n) +Z nonneg (succ n)) (nonneg (m *N succ n +N succ n)) (equalityCommutative (+Zinherits (m *N succ n) (succ n))) {r}) (symmetric (positiveEltPowerCollapse G r (m *N succ n) (succ n)))) (+WellDefined (positiveEltPowerMultiplies m (succ n) r) reflexive)))) (+WellDefined (transitive (symmetric (invTwice G _)) (inverseWellDefined G (symmetric (positiveEltPowerInverse m (r + positiveEltPower G r n))))) (symmetric (invTwice G _)))) (symmetric (invContravariant G))

positiveEltPowerHomAbelian : ({x y : A} → (x + y) ∼ (y + x)) → (x y : A) → (r : ℕ) → (positiveEltPower G (x + y) r) ∼ (positiveEltPower G x r + positiveEltPower G y r)
positiveEltPowerHomAbelian ab x y zero = symmetric identRight
positiveEltPowerHomAbelian ab x y (succ r) = transitive (symmetric +Associative) (transitive (+WellDefined reflexive (transitive (+WellDefined reflexive (positiveEltPowerHomAbelian ab x y r)) (transitive (+WellDefined reflexive ab) (transitive +Associative ab)))) +Associative)

elementPowerHomAbelian : ({x y : A} → (x + y) ∼ (y + x)) → (x y : A) → (r : ℤ) → (elementPower G (x + y) r) ∼ (elementPower G x r + elementPower G y r)
elementPowerHomAbelian ab x y (nonneg n) = positiveEltPowerHomAbelian ab x y n
elementPowerHomAbelian ab x y (negSucc n) = transitive (transitive (inverseWellDefined G (positiveEltPowerHomAbelian ab x y (succ n))) (inverseWellDefined G ab)) (invContravariant G)
