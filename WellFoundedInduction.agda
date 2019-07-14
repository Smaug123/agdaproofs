{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Functions

module WellFoundedInduction where
  data Accessible {a} {b} {A} (_<_ : Rel {a} {b} A) (x : A) : Set (lsuc a ⊔ b) where
    access : (∀ y → y < x → Accessible _<_ y) → Accessible _<_ x

  WellFounded : {a b : _} → ∀ {A} → Rel {a} {b} A → Set (lsuc a ⊔ b)
  WellFounded {a} _<_ = ∀ x → Accessible _<_ x

  foldAcc : {a b c : _} → {A : Set a} → {_<_ : Rel {a} {c} A} →
    (P : A → Set b) →
    (∀ x → (∀ y → y < x → P y) → P x) →
    ∀ z → Accessible _<_ z →
    P z
  foldAcc {a} {b} {c} {A} {_<_} P inductionProof = go
    where
      go : (z : A) → (Accessible _<_ z) → P z
      go z (access prf) = inductionProof z (λ y yLessZ → go y (prf y yLessZ))

  rec : {a b c : _} → {A : Set a} → {_<_ : Rel {a} {c} A} →
    WellFounded _<_ →
    (P : A → Set b) →
    (∀ x → (∀ y → y < x → P y) → P x) → (∀ z → P z)
  rec wf P inductionProof z = foldAcc P inductionProof _ (wf z)
