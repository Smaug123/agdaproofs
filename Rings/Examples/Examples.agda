{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Functions.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Integers.Integers
open import Numbers.Modulo.Group
open import Numbers.Modulo.Definition
open import Rings.Examples.Proofs
open import Numbers.Primes.PrimeNumbers
open import Setoids.Setoids
open import Rings.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Sets.EquivalenceRelations

module Rings.Examples.Examples where

multiplicationNotGroup : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ _*_ : A → A → A} (R : Ring S _+_ _*_) → (nontrivial : Setoid._∼_ S (Ring.1R R) (Ring.0R R) → False) → Group S _*_ → False
multiplicationNotGroup {S = S} R 1!=0 gr = exFalso (1!=0 (groupsHaveLeftCancellation gr (Ring.0R R) (Ring.1R R) (Ring.0R R) (transitive (Ring.timesZero' R) (symmetric (Ring.timesZero' R)))))
  where
    open Setoid S
    open Equivalence eq

nToZn : (n : ℕ) (pr : 0 <N n) (x : ℕ) → ℤn n pr
nToZn n pr x = nToZn' n pr x

mod : (n : ℕ) → (pr : 0 <N n) → ℤ → ℤn n pr
mod n pr a = mod' n pr a

modNExampleSurjective : (n : ℕ) → (pr : 0 <N n) → Surjection (mod n pr)
modNExampleSurjective n pr = modNExampleSurjective' n pr

{-
  modNExampleGroupHom : (n : ℕ) → (pr : 0 <N n) → GroupHom ℤGroup (ℤnGroup n pr) (mod n pr)
  modNExampleGroupHom n pr = modNExampleGroupHom' n pr

  embedZnInZ : {n : ℕ} {pr : 0 <N n} → (a : ℤn n pr) → ℤ
  embedZnInZ record { x = x } = nonneg x

  modNRoundTrip : (n : ℕ) → (pr : 0 <N n) → (a : ℤn n pr) → mod n pr (embedZnInZ a) ≡ a
  modNRoundTrip zero ()
  modNRoundTrip (succ n) pr record { x = x ; xLess = xLess } with divisionAlg (succ n) x
  modNRoundTrip (succ n) _ record { x = x ; xLess = xLess } | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = equalityZn _ _ p
    where
      p : rem ≡ x
      p = modIsUnique record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } record { quot = 0 ; rem = x ; pr = identityOfIndiscernablesLeft _ _ _ _≡_ refl (applyEquality (λ i → i +N x) (multiplicationNIsCommutative 0 n)) ; remIsSmall = inl xLess ; quotSmall = inl (succIsPositive n) }
  modNRoundTrip (succ n) _ record { x = x ; xLess = xLess } | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inr () }

-}
