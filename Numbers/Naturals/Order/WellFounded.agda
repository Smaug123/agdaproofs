{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Orders.WellFounded.Definition
open import Functions
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Semirings.Definition
open import Orders.Total.Definition

module Numbers.Naturals.Order.WellFounded where
open Semiring ℕSemiring

<NWellfounded : WellFounded _<N_
<NWellfounded = λ x → access (go x)
  where
    lemma : {a b c : ℕ} → a <N b → b <N succ c → a <N c
    lemma {a} {b} {c} (le y succYAeqB) (le z zbEqC') = le (y +N z) p
      where
        zbEqC : z +N b ≡ c
        zSuccYAEqC : z +N (succ y +N a) ≡ c
        zSuccYAEqC' : z +N (succ (y +N a)) ≡ c
        zSuccYAEqC'' : succ (z +N (y +N a)) ≡ c
        zSuccYAEqC''' : succ ((z +N y) +N a) ≡ c
        p : succ ((y +N z) +N a) ≡ c
        p = identityOfIndiscernablesLeft _≡_ zSuccYAEqC''' (applyEquality (λ n → succ (n +N a)) (commutative z y))
        zSuccYAEqC''' = identityOfIndiscernablesLeft _≡_ zSuccYAEqC'' (applyEquality succ (+Associative z y a))
        zSuccYAEqC'' = identityOfIndiscernablesLeft _≡_ zSuccYAEqC' (succExtracts z (y +N a))
        zSuccYAEqC' = identityOfIndiscernablesLeft _≡_ zSuccYAEqC (applyEquality (λ r → z +N r) refl)
        zbEqC = succInjective zbEqC'
        zSuccYAEqC = identityOfIndiscernablesLeft _≡_ zbEqC (applyEquality (λ r → z +N r) (equalityCommutative succYAeqB))
    go : ∀ n m → m <N n → Accessible _<N_ m
    go zero m (le x ())
    go (succ n) zero mLessN = access (λ y ())
    go (succ n) (succ m) smLessSN = access (λ o (oLessSM : o <N succ m) → go n o (lemma oLessSM smLessSN))
