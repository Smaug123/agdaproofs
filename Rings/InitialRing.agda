{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Fields.Fields
open import Rings.Orders.Total.Definition
open import Rings.Orders.Total.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Orders.LeastUpperBounds.Definition
open import Groups.Definition
open import Groups.Homomorphisms.Definition
open import Rings.Homomorphisms.Definition
open import Sets.EquivalenceRelations
open import Semirings.Definition

open import Numbers.Naturals.Semiring
open import Numbers.Integers.Definition
open import Numbers.Integers.RingStructure.Ring

module Rings.InitialRing {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open import Rings.Lemmas R
open import Groups.Lemmas additiveGroup

fromN : ℕ → A
fromN zero = 0R
fromN (succ n) = 1R + fromN n

fromNPreserves+ : (a b : ℕ) → fromN (a +N b) ∼ (fromN a) + (fromN b)
fromNPreserves+ zero b = symmetric identLeft
fromNPreserves+ (succ a) b = transitive (+WellDefined reflexive (fromNPreserves+ a b)) +Associative

fromNPreserves* : (a b : ℕ) → fromN (a *N b) ∼ (fromN a) * (fromN b)
fromNPreserves* zero b = symmetric (transitive *Commutative timesZero)
fromNPreserves* (succ a) b = transitive (transitive (fromNPreserves+ b (a *N b)) (+WellDefined (symmetric identIsIdent) (fromNPreserves* a b))) (symmetric *DistributesOver+')

fromNWellDefined : {a b : ℕ} → a ≡ b → fromN a ∼ fromN b
fromNWellDefined refl = reflexive

fromZ : ℤ → A
fromZ (nonneg x) = fromN x
fromZ (negSucc x) = inverse (fromN (succ x))

private
  lemma : (a : ℕ) → (b : ℕ) → (1R + fromN (succ a *N b +N a)) ∼ ((1R + fromN a) * (1R + fromN b))
  lemma a b = transitive (transitive (transitive (+WellDefined reflexive (transitive (fromNPreserves+ ((succ a) *N b) a) (transitive groupIsAbelian (+WellDefined reflexive (transitive (fromNPreserves+ b (a *N b)) (+WellDefined (symmetric identIsIdent) (fromNPreserves* a b))))))) +Associative) (+WellDefined (transitive (symmetric identIsIdent) *Commutative) (symmetric *DistributesOver+'))) (symmetric *DistributesOver+)

fromZPreserves+ : (a b : ℤ) → fromZ (a +Z b) ∼ (fromZ a) + (fromZ b)
fromZPreserves+ (nonneg zero) (nonneg y) = symmetric identLeft
fromZPreserves+ (nonneg (succ x)) (nonneg y) = transitive (+WellDefined reflexive (fromNPreserves+ x y)) +Associative
fromZPreserves+ (nonneg zero) (negSucc y) = symmetric identLeft
fromZPreserves+ (nonneg (succ x)) (negSucc zero) = transitive (transitive (transitive (transitive (symmetric identLeft) (+WellDefined (symmetric invLeft) reflexive)) (symmetric +Associative)) (+WellDefined (inverseWellDefined (symmetric identRight)) reflexive)) (groupIsAbelian)
fromZPreserves+ (nonneg (succ x)) (negSucc (succ y)) = transitive (fromZPreserves+ (nonneg x) (negSucc y)) (transitive (transitive (transitive (transitive (transitive (transitive (transitive (symmetric identLeft) +Associative) groupIsAbelian) (+WellDefined reflexive (+WellDefined (symmetric invLeft) reflexive))) (+WellDefined reflexive (symmetric +Associative))) +Associative) groupIsAbelian) (+WellDefined reflexive (symmetric invContravariant)))
fromZPreserves+ (negSucc zero) (nonneg zero) = symmetric identRight
fromZPreserves+ (negSucc zero) (nonneg (succ y)) = transitive (transitive (symmetric identLeft) (+WellDefined (symmetric (transitive (+WellDefined reflexive (symmetric identRight)) invLeft)) reflexive)) (symmetric +Associative)
fromZPreserves+ (negSucc (succ x)) (nonneg zero) = symmetric identRight
fromZPreserves+ (negSucc (succ x)) (nonneg (succ y)) = transitive (fromZPreserves+ (negSucc x) (nonneg y)) (transitive (transitive (+WellDefined reflexive (transitive (symmetric identLeft) (transitive (+WellDefined (symmetric invLeft) reflexive) (symmetric +Associative)))) +Associative) (+WellDefined (symmetric invContravariant) reflexive))
fromZPreserves+ (negSucc x) (negSucc y) = transitive (transitive invContravariant (transitive (+WellDefined invContravariant reflexive) (transitive (+WellDefined (transitive (transitive (+WellDefined (transitive (inverseWellDefined (fromNPreserves+ x y)) invContravariant) reflexive) (symmetric +Associative)) groupIsAbelian) reflexive) (symmetric +Associative)))) (+WellDefined (symmetric invContravariant) (symmetric invContravariant))

fromZPreserves* : (a b : ℤ) → fromZ (a *Z b) ∼ (fromZ a) * (fromZ b)
fromZPreserves* (nonneg a) (nonneg b) = fromNPreserves* a b
fromZPreserves* (nonneg zero) (negSucc b) = symmetric (transitive *Commutative timesZero)
fromZPreserves* (nonneg (succ a)) (negSucc b) = transitive (inverseWellDefined (lemma a b)) (symmetric ringMinusExtracts)
fromZPreserves* (negSucc a) (nonneg zero) = symmetric timesZero
fromZPreserves* (negSucc a) (nonneg (succ b)) = transitive (inverseWellDefined (transitive (+WellDefined reflexive (fromNWellDefined {(a +N b *N a) +N b} {(b +N a *N b) +N a} (transitivity (Semiring.commutative ℕSemiring _ b) (transitivity (applyEquality (b +N_) (transitivity (Semiring.commutative ℕSemiring a _) (applyEquality (_+N a) (multiplicationNIsCommutative b a)))) (Semiring.+Associative ℕSemiring b _ a))))) (lemma a b))) (symmetric ringMinusExtracts')
fromZPreserves* (negSucc a) (negSucc b) = transitive (transitive (+WellDefined reflexive (fromNWellDefined {b +N a *N succ b} {(b +N a *N b) +N a} (transitivity (applyEquality (b +N_) (transitivity (multiplicationNIsCommutative a (succ b)) (transitivity (Semiring.commutative ℕSemiring a _) (applyEquality (_+N a) (multiplicationNIsCommutative b a))))) (Semiring.+Associative ℕSemiring b _ a)))) (lemma a b)) (symmetric twoNegativesTimes)

ringHom : RingHom ℤRing R fromZ
RingHom.preserves1 ringHom = identRight
RingHom.ringHom ringHom {r} {s} = fromZPreserves* r s
GroupHom.groupHom (RingHom.groupHom ringHom) {r} {s} = fromZPreserves+ r s
GroupHom.wellDefined (RingHom.groupHom ringHom) refl = reflexive
