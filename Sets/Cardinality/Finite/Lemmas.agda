{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas

module Sets.Cardinality.Finite.Lemmas where

finsetInjectIntoℕ : {n : ℕ} → Injection (toNat {n})
Injection.property (finsetInjectIntoℕ {zero}) {()}
finsetInjectIntoℕ {succ n} = record { property = ans }
  where
    ans : {n : ℕ} → {x y : FinSet (succ n)} → (toNat x ≡ toNat y) → x ≡ y
    ans {zero} {fzero} {fzero} _ = refl
    ans {zero} {fzero} {fsucc ()}
    ans {zero} {fsucc ()} {y}
    ans {succ n} {fzero} {fzero} pr = refl
    ans {succ n} {fzero} {fsucc y} ()
    ans {succ n} {fsucc x} {fzero} ()
    ans {succ n} {fsucc x} {fsucc y} pr with succInjective pr
    ... | pr' = applyEquality fsucc (ans {n} {x} {y} pr')
