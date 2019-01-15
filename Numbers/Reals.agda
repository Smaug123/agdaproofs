{-# OPTIONS --safe --warning=error #-}

open import Fields.Fields
open import Functions
open import Orders
open import LogicalFormulae
open import Numbers.Rationals
open import Numbers.Naturals

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Numbers.Reals where
  record ℝ : Set where
    field
      f : ℕ → ℚ
      converges : {ε : ℚ} → Sg ℕ (λ x → {y : ℕ} → x <N y → ((f x) +Q (f y)) <Q ε)

  _+R_ : ℝ → ℝ → ℝ
  ℝ.f (record { f = a ; converges = conA } +R record { f = b ; converges = conB }) n = (a n) +Q (b n)
  ℝ.converges (record { f = a ; converges = conA } +R record { f = b ; converges = conB }) {e} = {!!}

  _*R_ : ℝ → ℝ → ℝ
  ℝ.f (record { f = a ; converges = conA } *R record { f = b ; converges = conB }) n = (a n) *Q (b n)
  ℝ.converges (record { f = a ; converges = conA } *R record { f = b ; converges = conB}) {e} = {!!}
