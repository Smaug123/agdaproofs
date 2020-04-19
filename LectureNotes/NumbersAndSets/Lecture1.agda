{-# OPTIONS --warning=error --safe --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Numbers.Integers.Integers
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Subtraction
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Numbers.Naturals.Exponentiation
open import Numbers.Primes.PrimeNumbers
open import Maybe
open import Semirings.Definition
import Semirings.Solver

open module NatSolver = Semirings.Solver ℕSemiring multiplicationNIsCommutative

module LectureNotes.NumbersAndSets.Lecture1 where

a-Na : (a : ℕ) → a -N' a ≡ yes 0
a-Na zero = refl
a-Na (succ a) = a-Na a

-N''lemma : (a b : ℕ) → (a<b : a ≤N b) → b -N' a ≡ yes (subtractionNResult.result (-N a<b))
-N''lemma zero (succ b) (inl x) = refl
-N''lemma (succ a) (succ b) (inl x) = -N''lemma a b (inl (canRemoveSuccFrom<N x))
-N''lemma a b (inr x) rewrite x | a-Na b = ans
  where
    ans : yes 0 ≡ yes (subtractionNResult.result (-N (inr (refl {x = b}))))
    ans with -N (inr (refl {x = b}))
    ans | record { result = result ; pr = pr } with result
    ans | record { result = result ; pr = pr } | zero = refl
    ans | record { result = result ; pr = pr } | succ bl = exFalso (cannotAddAndEnlarge'' pr)

-N'' : (a b : ℕ) (a<b : a ≤N b) → ℕ
-N'' a b a<b with -N''lemma a b a<b
... | bl with b -N' a
-N'' a b a<b | bl | yes x = x

n3Bigger : (n : ℕ) → (n ≡ 0) || (n ≤N n ^N 3)
n3Bigger n = exponentiationIncreases n 2

n3Bigger' : (n : ℕ) → n ≤N n ^N 3
n3Bigger' zero = inr refl
n3Bigger' (succ n) with n3Bigger (succ n)
n3Bigger' (succ n) | inr f = f

-- How to use the semiring solver
-- The process is very mechanical; I haven't yet worked out how to do reflection,
-- so there's quite a bit of transcribing expressions into the Expr form.
-- The first two arguments to from-to-by are totally mindless in construction.
proof : (n : ℕ) → ((n *N n) +N ((2 *N n) +N 1)) ≡ (n +N 1) *N (n +N 1)
proof n =
  from plus (times (const n) (const n)) (plus (times (succ (succ zero)) (const n)) (succ zero))
  to times (plus (const n) (succ zero)) (plus (const n) (succ zero))
  by
    applyEquality (λ i → succ (n *N n) +N (n +N i)) ((from (const n) to (plus (const n) zero) by refl))
