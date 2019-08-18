{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae

module Numbers.Naturals.Definition where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infix 100 succ

{-# BUILTIN NATURAL ℕ #-}

succInjective : {a b : ℕ} → (succ a ≡ succ b) → a ≡ b
succInjective {a} {.a} refl = refl
