{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import WellFoundedInduction
open import Functions
open import Orders
open import Numbers.Naturals

module Numbers.NaturalsWithK where

<NRefl : {a b : ℕ} → (p1 p2 : a <N b) → (p1 ≡ p2)
<NRefl {a} {.(succ (p1 +N a))} (le p1 refl) (le p2 proof2) = help p1=p2 proof2
  where
    p1=p2 : p1 ≡ p2
    p1=p2 = equalityCommutative (canSubtractFromEqualityRight {p2} {a} {p1} (succInjective proof2))
    help : (p1 ≡ p2) → (pr2 : succ (p2 +N a) ≡ succ (p1 +N a)) → le p1 refl ≡ le p2 pr2
    help refl refl = refl
