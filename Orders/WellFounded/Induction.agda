{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Orders.WellFounded.Definition

module Orders.WellFounded.Induction {a b : _} {A : Set a} {_<_ : Rel {a} {b} A} (wf : WellFounded _<_) where

private
  foldAcc :
    {c : _}
    (P : A → Set c) →
    (∀ x → (∀ y → y < x → P y) → P x) →
    ∀ z → Accessible _<_ z →
    P z
  foldAcc P inductionProof = go
    where
      go : (z : A) → (Accessible _<_ z) → P z
      go z (access prf) = inductionProof z (λ y yLessZ → go y (prf y yLessZ))

rec :
  {c : _}
  (P : A → Set c) →
  (∀ x → (∀ y → y < x → P y) → P x) → (∀ z → P z)
rec P inductionProof z = foldAcc P inductionProof _ (wf z)
