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

naughtE : {a : ℕ} → zero ≡ succ a → False
naughtE ()

aIsNotSuccA : (a : ℕ) → (a ≡ succ a) → False
aIsNotSuccA zero pr = naughtE pr
aIsNotSuccA (succ a) pr = aIsNotSuccA a (succInjective pr)

ℕDecideEquality : (a b : ℕ) → ((a ≡ b) || ((a ≡ b) → False))
ℕDecideEquality zero zero = inl refl
ℕDecideEquality zero (succ b) = inr (λ ())
ℕDecideEquality (succ a) zero = inr (λ ())
ℕDecideEquality (succ a) (succ b) with ℕDecideEquality a b
ℕDecideEquality (succ a) (succ b) | inl x = inl (applyEquality succ x)
ℕDecideEquality (succ a) (succ b) | inr x = inr λ pr → x (succInjective pr)
