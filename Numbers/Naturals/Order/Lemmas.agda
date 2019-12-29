{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Semirings.Definition
open import Numbers.Naturals.Order
open import Numbers.Naturals.Semiring

module Numbers.Naturals.Order.Lemmas where
open Semiring ℕSemiring

inequalityShrinkRight : {a b c : ℕ} → a +N b <N c → b <N c
inequalityShrinkRight {a} {b} {c} (le x proof) = le (x +N a) (transitivity (applyEquality succ (equalityCommutative (Semiring.+Associative ℕSemiring x a b))) proof)

inequalityShrinkLeft : {a b c : ℕ} → a +N b <N c → a <N c
inequalityShrinkLeft {a} {b} {c} (le x proof) = le (x +N b) (transitivity (applyEquality succ (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring x b a)) (applyEquality (x +N_) (Semiring.commutative ℕSemiring b a)))) proof)

productCancelsRight : (a b c : ℕ) → (zero <N a) → (b *N a ≡ c *N a) → (b ≡ c)
productCancelsRight a zero zero aPos eq = refl
productCancelsRight zero zero (succ c) (le x ()) eq
productCancelsRight (succ a) zero (succ c) aPos eq = contr
  where
    h : zero ≡ succ c *N succ a
    h = eq
    contr : zero ≡ succ c
    contr = exFalso (naughtE h)
productCancelsRight zero (succ b) zero (le x ()) eq
productCancelsRight (succ a) (succ b) zero aPos eq = contr
  where
    h : succ b *N succ a ≡ zero
    h = eq
    contr : succ b ≡ zero
    contr = exFalso (naughtE (equalityCommutative h))
productCancelsRight zero (succ b) (succ c) (le x ()) eq
productCancelsRight (succ a) (succ b) (succ c) aPos eq = applyEquality succ (productCancelsRight (succ a) b c aPos l)
    where
      i : succ a +N b *N succ a ≡ succ c *N succ a
      i = eq
      j : succ c *N succ a ≡ succ a +N c *N succ a
      j = refl
      k : succ a +N b *N succ a ≡ succ a +N c *N succ a
      k = transitivity i j
      l : b *N succ a ≡ c *N succ a
      l = canSubtractFromEqualityLeft {succ a} {b *N succ a} {c *N succ a} k

productCancelsLeft : (a b c : ℕ) → (zero <N a) → (a *N b ≡ a *N c) → (b ≡ c)
productCancelsLeft a b c aPos pr = productCancelsRight a b c aPos j
  where
    i : b *N a ≡ a *N c
    i = identityOfIndiscernablesLeft _≡_ pr (multiplicationNIsCommutative a b)
    j : b *N a ≡ c *N a
    j = identityOfIndiscernablesRight _≡_ i (multiplicationNIsCommutative a c)

productCancelsRight' : (a b c : ℕ) → (b *N a ≡ c *N a) → (a ≡ zero) || (b ≡ c)
productCancelsRight' zero b c pr = inl refl
productCancelsRight' (succ a) b c pr = inr (productCancelsRight (succ a) b c (succIsPositive a) pr)

productCancelsLeft' : (a b c : ℕ) → (a *N b ≡ a *N c) → (a ≡ zero) || (b ≡ c)
productCancelsLeft' zero b c pr = inl refl
productCancelsLeft' (succ a) b c pr = inr (productCancelsLeft (succ a) b c (succIsPositive a) pr)

subtractionPreservesInequality : {a b : ℕ} → (c : ℕ) → a +N c <N b +N c → a <N b
subtractionPreservesInequality {a} {b} zero prABC rewrite commutative a 0 | commutative b 0 = prABC
subtractionPreservesInequality {a} {b} (succ c) (le x proof) = le x (canSubtractFromEqualityRight {b = succ c} (transitivity (equalityCommutative (+Associative (succ x) a (succ c))) proof))

cancelInequalityLeft : {a b c : ℕ} → a *N b <N a *N c → b <N c
cancelInequalityLeft {a} {zero} {zero} (le x proof) rewrite (productZeroRight a) = exFalso (naughtE (equalityCommutative proof))
cancelInequalityLeft {a} {zero} {succ c} pr = succIsPositive c
cancelInequalityLeft {a} {succ b} {zero} (le x proof) rewrite (productZeroRight a) = exFalso (naughtE (equalityCommutative proof))
cancelInequalityLeft {a} {succ b} {succ c} pr = succPreservesInequality q'
  where
    p' : succ b *N a <N succ c *N a
    p' = canFlipMultiplicationsInIneq {a} {succ b} {a} {succ c} pr
    p'' : b *N a +N a <N succ c *N a
    p'' = identityOfIndiscernablesLeft _<N_ p' (commutative a (b *N a))
    p''' : b *N a +N a <N c *N a +N a
    p''' = identityOfIndiscernablesRight _<N_ p'' (commutative a (c *N a))
    p : b *N a <N c *N a
    p = subtractionPreservesInequality a p'''
    q : a *N b <N a *N c
    q = canFlipMultiplicationsInIneq {b} {a} {c} {a} p
    q' : b <N c
    q' = cancelInequalityLeft {a} {b} {c} q
