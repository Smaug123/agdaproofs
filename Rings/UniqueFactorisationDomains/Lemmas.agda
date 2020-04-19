{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Rings.Definition
open import Rings.IntegralDomains.Definition
open import Vectors
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Definition
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Rings.UniqueFactorisationDomains.Lemmas {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} {R : Ring S _+_ _*_} (intDom : IntegralDomain R) where

open import Rings.Units.Definition R
open import Rings.Irreducibles.Definition intDom
open import Rings.Associates.Definition intDom
open import Rings.Primes.Definition intDom
open import Rings.Divisible.Definition R
open import Rings.Divisible.Lemmas R
open import Rings.UniqueFactorisationDomains.Definition intDom
open Ring R
open Setoid S
open Equivalence eq

ufdImpliesUfd' : UFD → UFD'
UFD'.factorisation (ufdImpliesUfd' x) = UFD.factorisation x
Prime.isPrime (UFD'.irreduciblesArePrime (ufdImpliesUfd' ufd) {r} irreducible) a b (s , ab=rs) rNotDivA = {!!}
  where
  -- we can't factorise a, it might be a unit :(
    factA : Factorisation {a} (λ p → rNotDivA (divisibleWellDefined reflexive (symmetric p) (everythingDividesZero r))) {!!}
    factA = UFD.factorisation ufd {a} {!!} {!!}
    fact1 : Factorisation {r} {!!} {!!}
    fact1 = {!!}
    fact2 : Factorisation {r} {!!} {!!}
    fact2 = {!!}
Prime.nonzero (UFD'.irreduciblesArePrime (ufdImpliesUfd' x) irreducible) = Irreducible.nonzero irreducible
Prime.nonunit (UFD'.irreduciblesArePrime (ufdImpliesUfd' x) irreducible) = Irreducible.nonunit irreducible

private
  lemma2 : UFD' → {r : A} → .(nonzero : (r ∼ 0R) → False) .(nonunit : (Unit r) → False) → (f1 f2 : Factorisation {r} nonzero nonunit) → factorisationEquality f1 f2
  lemma2 x nonzero nonunit record { len = lenA ; factorise = factoriseA ; factoriseIsFactorisation = factoriseIsFactorisationA ; factoriseIsIrreducibles = factoriseIsIrreduciblesA ; distinct = distinctA } record { len = lenB ; factorise = factoriseB ; factoriseIsFactorisation = factoriseIsFactorisationB ; factoriseIsIrreducibles = factoriseIsIrreduciblesB ; distinct = distinctB } with ℕDecideEquality lenA lenB
  lemma2 x nonzero nonunit record { len = zero ; factorise = [] ; factoriseIsFactorisation = factoriseIsFactorisationA ; factoriseIsIrreducibles = factoriseIsIrreduciblesA ; distinct = distinctA } record { len = .0 ; factorise = [] ; factoriseIsFactorisation = factoriseIsFactorisationB ; factoriseIsIrreducibles = factoriseIsIrreduciblesB ; distinct = distinctB } | inl refl = record {}
  lemma2 ufd' {r} nonzero nonunit record { len = (succ len) ; factorise = (a1 ,, n1) ,- factoriseA ; factoriseIsFactorisation = factoriseIsFactorisationA ; factoriseIsIrreducibles = factoriseIsIrreduciblesA ; distinct = distinctA } record { len = .(succ len) ; factorise = factoriseB ; factoriseIsFactorisation = factoriseIsFactorisationB ; factoriseIsIrreducibles = factoriseIsIrreduciblesB ; distinct = distinctB } | inl refl = {!!}
    where
      a1Prime : Prime a1
      a1Prime = UFD'.irreduciblesArePrime ufd' (_&&_.fst factoriseIsIrreduciblesA)
      a1DivR : a1 ∣ r
      a1DivR = {!!}

  ... | inr neq = {!!}

ufd'ImpliesUfd : UFD' → UFD
UFD.factorisation (ufd'ImpliesUfd x) = UFD'.factorisation x
UFD.uniqueFactorisation (ufd'ImpliesUfd x) {r} nonzero nonunit f1 f2 = lemma2 x nonzero nonunit f1 f2
