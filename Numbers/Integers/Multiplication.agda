{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Integers.Definition

module Numbers.Integers.Multiplication where

infix 25 _*Z_
_*Z_ : ℤ → ℤ → ℤ
nonneg x *Z nonneg y = nonneg (x *N y)
nonneg zero *Z negSucc y = nonneg zero
nonneg (succ x) *Z negSucc y = negSucc ((succ x) *N y +N x)
negSucc x *Z nonneg zero = nonneg zero
negSucc x *Z nonneg (succ y) = negSucc ((succ y) *N x +N y)
negSucc x *Z negSucc y = nonneg ((succ x) *N (succ y))

*ZInherits : (a b : ℕ) → nonneg (a *N b) ≡ (nonneg a) *Z (nonneg b)
*ZInherits a b = refl
