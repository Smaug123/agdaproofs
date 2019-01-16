{-# OPTIONS --safe --warning=error #-}

open import Fields.Fields
open import Functions
open import Orders
open import LogicalFormulae
open import Numbers.Rationals
open import Numbers.RationalsLemmas
open import Numbers.Naturals
open import Setoids.Setoids
open import Setoids.Orders

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Numbers.Reals where
  record ℝ : Set where
    field
      f : ℕ → ℚ
      converges : {ε : ℚ} → Sg ℕ (λ x → {y : ℕ} → x <N y → (absQ ((f x) -Q (f y))) <Q ε)

  _+R_ : ℝ → ℝ → ℝ
  ℝ.f (record { f = a ; converges = conA } +R record { f = b ; converges = conB }) n = (a n) +Q (b n)
  ℝ.converges (record { f = a ; converges = conA } +R record { f = b ; converges = conB }) {e} = {!absQ (a x +Q b x)!}

  negateR : ℝ → ℝ
  ℝ.f (negateR record { f = f ; converges = converges }) n = negateQ (f n)
  ℝ.converges (negateR record { f = f ; converges = converges }) {e} with converges {e}
  ... | n , pr = n , λ {y} x<y → SetoidPartialOrder.wellDefined ℚPartialOrder {absQ ((f n) -Q (f y))} {absQ ((negateQ (f n)) -Q (negateQ (f y)))} {e} {e} {!!} {!reflQ e!} (pr {y} x<y)

  _-R_ : ℝ → ℝ → ℝ
  a -R b = a +R (negateR b)

  _*R_ : ℝ → ℝ → ℝ
  ℝ.f (record { f = a ; converges = conA } *R record { f = b ; converges = conB }) n = (a n) *Q (b n)
  ℝ.converges (record { f = a ; converges = conA } *R record { f = b ; converges = conB}) {e} = {!!}

  realsSetoid : Setoid ℝ
  (realsSetoid Setoid.∼ record { f = a ; converges = convA }) record { f = b ; converges = convB } = {!!}
  Setoid.eq realsSetoid = {!!}
