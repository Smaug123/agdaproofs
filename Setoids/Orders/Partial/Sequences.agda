{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Orders.Total.Definition
open import Orders.Partial.Definition
open import Setoids.Setoids
open import Functions
open import Sequences
open import Setoids.Orders.Partial.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Setoids.Orders.Partial.Sequences {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_<_ : Rel {a} {c} A} (p : SetoidPartialOrder S _<_) where

open SetoidPartialOrder p

WeaklyIncreasing' : (Sequence A) → Set (b ⊔ c)
WeaklyIncreasing' s = (m n : ℕ) → (m <N n) → (index s m) <= (index s n)

WeaklyIncreasing : (Sequence A) → Set (b ⊔ c)
WeaklyIncreasing s = (m : ℕ) → (index s m) <= index s (succ m)

tailRespectsWeaklyIncreasing : (a : Sequence A) → WeaklyIncreasing a → WeaklyIncreasing (Sequence.tail a)
tailRespectsWeaklyIncreasing a incr m = incr (succ m)

weaklyIncreasingImplies' : (a : Sequence A) → WeaklyIncreasing a → WeaklyIncreasing' a
weaklyIncreasingImplies' a x zero (succ zero) m<n = x 0
weaklyIncreasingImplies' a x zero (succ (succ n)) m<n = <=Transitive (weaklyIncreasingImplies' a x zero (succ n) (succIsPositive n)) (x (succ n))
weaklyIncreasingImplies' a x (succ m) (succ n) m<n = weaklyIncreasingImplies' (Sequence.tail a) (tailRespectsWeaklyIncreasing a x) m n (canRemoveSuccFrom<N m<n)

weaklyIncreasing'Implies : (a : Sequence A) → WeaklyIncreasing' a → WeaklyIncreasing a
weaklyIncreasing'Implies a incr m = incr m (succ m) (le 0 refl)

StrictlyIncreasing' : (Sequence A) → Set (c)
StrictlyIncreasing' s = (m n : ℕ) → (m <N n) → (index s m) < (index s n)

StrictlyIncreasing : (Sequence A) → Set (c)
StrictlyIncreasing s = (m : ℕ) → (index s m) < index s (succ m)

tailRespectsStrictlyIncreasing : (a : Sequence A) → StrictlyIncreasing a → StrictlyIncreasing (Sequence.tail a)
tailRespectsStrictlyIncreasing a incr m = incr (succ m)

strictlyIncreasingImplies' : (a : Sequence A) → StrictlyIncreasing a → StrictlyIncreasing' a
strictlyIncreasingImplies' a x zero (succ zero) m<n = x 0
strictlyIncreasingImplies' a x zero (succ (succ n)) m<n = <Transitive (strictlyIncreasingImplies' a x zero (succ n) (succIsPositive n)) (x (succ n))
strictlyIncreasingImplies' a x (succ m) (succ n) m<n = strictlyIncreasingImplies' (Sequence.tail a) (tailRespectsStrictlyIncreasing a x) m n (canRemoveSuccFrom<N m<n)

strictlyIncreasing'Implies : (a : Sequence A) → StrictlyIncreasing' a → StrictlyIncreasing a
strictlyIncreasing'Implies a incr m = incr m (succ m) (le 0 refl)
