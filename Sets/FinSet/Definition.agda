{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition

module Sets.FinSet.Definition where

data FinSet : (n : ℕ) → Set where
  fzero : {n : ℕ} → FinSet (succ n)
  fsucc : {n : ℕ} → FinSet n → FinSet (succ n)

fsuccInjective : {n : ℕ} → {a b : FinSet n} → fsucc a ≡ fsucc b → a ≡ b
fsuccInjective refl = refl

data FinNotEquals : {n : ℕ} → (a b : FinSet (succ n)) → Set where
  fne2 : (a b : FinSet 2) → ((a ≡ fzero) && (b ≡ fsucc (fzero))) || ((b ≡ fzero) && (a ≡ fsucc (fzero))) → FinNotEquals {1} a b
  fneN : {n : ℕ} → (a b : FinSet (succ (succ (succ n)))) → (((a ≡ fzero) && (Sg (FinSet (succ (succ n))) (λ c → b ≡ fsucc c))) || ((Sg (FinSet (succ (succ n))) (λ c → a ≡ fsucc c)) && (b ≡ fzero))) || (Sg (FinSet (succ (succ n)) && FinSet (succ (succ n))) (λ t → (a ≡ fsucc (_&&_.fst t)) & (b ≡ fsucc (_&&_.snd t)) & FinNotEquals (_&&_.fst t) (_&&_.snd t))) → FinNotEquals {succ (succ n)} a b
