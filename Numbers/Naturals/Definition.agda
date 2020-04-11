{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Decidable.Lemmas

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

ℕDecideEquality' : (a b : ℕ) → Bool
ℕDecideEquality' a b with ℕDecideEquality a b
ℕDecideEquality' a b | inl x = BoolTrue
ℕDecideEquality' a b | inr x = BoolFalse

record _=N'_ (a b : ℕ) : Set where
  field
    .eq : a ≡ b

squashN : {a b : ℕ} → a =N' b → a ≡ b
squashN record { eq = eq } = squash ℕDecideEquality eq

collapseN : {a b : ℕ} → a ≡ b → a =N' b
collapseN refl = record { eq = refl }

=N'Refl : {a b : ℕ} → (p1 p2 : a =N' b) → p1 ≡ p2
=N'Refl p1 p2 = refl
