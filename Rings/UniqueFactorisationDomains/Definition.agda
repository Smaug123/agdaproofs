{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Vectors
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.UniqueFactorisationDomains.Definition {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Units.Definition R
open import Rings.Irreducibles.Definition intDom
open import Rings.Associates.Definition intDom
open import Rings.Primes.Definition intDom
open Ring R
open Setoid S

private
  power : A → ℕ → A
  power x zero = 1R
  power x (succ n) = x * power x n

  allDistinct : {n : ℕ} → Vec A n → Set (a ⊔ b)
  allDistinct [] = True'
  allDistinct (x ,- xs) = (allDistinct xs) && vecAllTrue (λ n → (n ∼ x) → False) xs

record Factorisation {r : A} .(nonzero : (r ∼ 0R) → False) .(nonunit : (Unit r) → False) : Set (a ⊔ b) where
  field
    len : ℕ
    factorise : Vec (A && ℕ) len
    factoriseIsFactorisation : vecFold (λ x y → y * power (_&&_.fst x) (succ (_&&_.snd x))) 1R factorise ∼ r
    factoriseIsIrreducibles : vecAllTrue Irreducible (vecMap _&&_.fst factorise)
    distinct : allDistinct (vecMap _&&_.fst factorise)

private
  equality : {n : ℕ} (v1 v2 : Vec (A && ℕ) n) → Set (a ⊔ b)
  equality [] [] = True'
  equality {succ n} ((a ,, an) ,- v1) v2 = Sg ℕ (λ index → Sg (index <N succ n) (λ i<n → (Associates (_&&_.fst (vecIndex v2 index i<n)) a) && ((_&&_.snd (vecIndex v2 index i<n) ≡ an) && equality v1 (vecDelete index i<n v2))))

factorisationEquality : {r : A} → .{nonzero : (r ∼ 0R) → False} → .{nonunit : (Unit r) → False} → Factorisation nonzero nonunit → Factorisation nonzero nonunit → Set (a ⊔ b)
factorisationEquality record { len = lenA ; factorise = factoriseA ; factoriseIsFactorisation = factoriseIsFactorisationA ; factoriseIsIrreducibles = factoriseIsIrreduciblesA ; distinct = distinctA } record { len = lenB ; factorise = factoriseB ; factoriseIsFactorisation = factoriseIsFactorisationB ; factoriseIsIrreducibles = factoriseIsIrreduciblesB ; distinct = distinctB } with ℕDecideEquality lenA lenB
factorisationEquality record { len = a ; factorise = factoriseA } record { len = .a ; factorise = factoriseB } | inl refl = equality factoriseA factoriseB
factorisationEquality record { len = a ; factorise = factoriseA } record { len = b ; factorise = factoriseB } | inr _ = False'

record UFD : Set (a ⊔ b) where
  field
    factorisation : {r : A} → (nonzero : (r ∼ 0R) → False) → (nonunit : (Unit r) → False) → Factorisation nonzero nonunit
    uniqueFactorisation : {r : A} → (nonzero : (r ∼ 0R) → False) → (nonunit : (Unit r) → False) → (f1 f2 : Factorisation nonzero nonunit) → factorisationEquality f1 f2

record UFD' : Set (a ⊔ b) where
  field
    factorisation : {r : A} → (nonzero : (r ∼ 0R) → False) → (nonunit : (Unit r) → False) → Factorisation nonzero nonunit
    irreduciblesArePrime : {r : A} → Irreducible r → Prime r
