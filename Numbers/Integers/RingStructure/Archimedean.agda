{-# OPTIONS --safe --warning=error --without-K #-}

open import Semirings.Definition
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Integers.RingStructure.Ring
open import Groups.Orders.Archimedean
open import Rings.Orders.Partial.Definition
open import Numbers.Integers.Order

module Numbers.Integers.RingStructure.Archimedean where

open import Groups.Cyclic.Definition ℤGroup
open import Semirings.Solver ℕSemiring multiplicationNIsCommutative

private
  lemma : (x y : ℕ) → positiveEltPower (nonneg x) y ≡ nonneg (x *N y)
  lemma x zero rewrite Semiring.productZeroRight ℕSemiring x = refl
  lemma x (succ y) rewrite lemma x y | multiplicationNIsCommutative x (succ y) | multiplicationNIsCommutative y x = equalityCommutative (+Zinherits x (x *N y))

ℤArchimedean : Archimedean (toGroup ℤRing ℤPOrderedRing)
ℤArchimedean (nonneg (succ a)) (nonneg (succ b)) 0<a 0<b = succ (succ b) , t
  where
    v : b +N (a +N (a +N a *N b)) ≡ a +N (a +N (b +N a *N b))
    v rewrite Semiring.+Associative ℕSemiring a a (a *N b) | Semiring.+Associative ℕSemiring b (a +N a) (a *N b) | Semiring.+Associative ℕSemiring a b (a *N b) | Semiring.+Associative ℕSemiring a (a +N b) (a *N b) | Semiring.commutative ℕSemiring b (a +N a) | Semiring.+Associative ℕSemiring a a b = refl
    u : succ ((a +N (a +N a *N b)) +N b) ≡ a +N succ (a +N (b +N a *N b))
    u = from (succ (plus (plus (const a) (plus (const a) (times (const a) (const b)))) (const b))) to (plus (const a) (succ (plus (const a) (plus (const b) (times (const a) (const b)))))) by applyEquality succ v
    t : nonneg (succ b) <Z nonneg (succ a) +Z (nonneg (succ a) +Z positiveEltPower (nonneg (succ a)) b)
    t rewrite lemma (succ a) b = lessInherits (succPreservesInequality (le (a +N (a +N a *N b)) u))
