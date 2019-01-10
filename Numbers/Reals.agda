{-# OPTIONS --safe --warning=error #-}

open import Fields
open import Rings
open import Functions
open import Orders
open import LogicalFormulae
open import Rationals
open import Naturals

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Reals where
  record Subset {m n : _} (A : Set m) (B : Set n) : Set (m ⊔ n) where
    field
      inj : A → B
      injInj : Injection inj

  --record RealField {n : _} {A : Set n} {R : Ring A} {F : Field R} : Set _ where
  --  field
  --    orderedField : OrderedField F
  --  open OrderedField orderedField
  --  open TotalOrder ord
  --  open Ring R
  --  field
  --    complete : {c : _} {C : Set c} → (S : Subset C A) → (upperBound : A) → ({s : C} → (Subset.inj S s) < upperBound) → Sg A (λ lub → ({s : C} → (Subset.inj S s) < lub) && ({s : C} → (Subset.inj S s) < upperBound → (Subset.inj S s) < lub))


  record Real : Set where
    field
      f : ℕ → ℚ
      converges : {ε : ℚ} → Sg ℕ (λ x → {y : ℕ} → x <N y → (f x) +Q (f y) <Q ε)
