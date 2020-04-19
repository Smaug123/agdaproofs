{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition

module Numbers.Integers.Definition where

data ℤ : Set where
  nonneg : ℕ → ℤ
  negSucc : ℕ → ℤ
{-# BUILTIN INTEGER       ℤ       #-}
{-# BUILTIN INTEGERPOS    nonneg  #-}
{-# BUILTIN INTEGERNEGSUC negSucc #-}

nonnegInjective : {a b : ℕ} → nonneg a ≡ nonneg b → a ≡ b
nonnegInjective refl = refl

negSuccInjective : {a b : ℕ} → negSucc a ≡ negSucc b → a ≡ b
negSuccInjective refl = refl

ℤDecideEquality : (a b : ℤ) → ((a ≡ b) || ((a ≡ b) → False))
ℤDecideEquality (nonneg x) (nonneg y) with ℕDecideEquality x y
ℤDecideEquality (nonneg x) (nonneg y) | inl eq = inl (applyEquality nonneg eq)
ℤDecideEquality (nonneg x) (nonneg y) | inr non = inr λ i → non (nonnegInjective i)
ℤDecideEquality (nonneg x) (negSucc y) = inr λ ()
ℤDecideEquality (negSucc x) (nonneg x₁) = inr λ ()
ℤDecideEquality (negSucc x) (negSucc y) with ℕDecideEquality x y
ℤDecideEquality (negSucc x) (negSucc y) | inl eq = inl (applyEquality negSucc eq)
ℤDecideEquality (negSucc x) (negSucc y) | inr non = inr λ i → non (negSuccInjective i)
