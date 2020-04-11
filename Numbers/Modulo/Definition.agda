{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module Numbers.Modulo.Definition where

record ℤn (n : ℕ) .(pr : 0 <N n) : Set where
  field
    x : ℕ
    .xLess : x <N n

equalityZn : {n : ℕ} .{pr : 0 <N n} → {a b : ℤn n pr} → (ℤn.x a ≡ ℤn.x b) → a ≡ b
equalityZn {a = record { x = a ; xLess = aLess }} {record { x = .a ; xLess = bLess }} refl = refl
