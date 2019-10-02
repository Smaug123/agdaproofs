{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Orders
open import Groups.Groups
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.WithK
open import Numbers.Primes.PrimeNumbers
open import Rings.Definition
open import Setoids.Setoids
open import Numbers.Modulo.IntegersModN
open import Semirings.Definition

module IntegersModNRing where
  modNToℕ : {n : ℕ} {pr : 0 <N n} → (a : ℤn n pr) → ℕ
  modNToℕ record { x = x ; xLess = xLess } = x

  *nhelper : {n : ℕ} {pr : 0 <N n} → (max : ℕ) → (a : ℤn n pr) → ℤn n pr → (max ≡ modNToℕ a) → ℤn n pr
  *nhelper {zero} {()}
  *nhelper {succ n} zero a b pr2 = record { x = 0 ; xLess = succIsPositive n }
  *nhelper {succ n} (succ max) record { x = zero ; xLess = xLess } b ()
  *nhelper {succ n} (succ max) record { x = (succ x) ; xLess = xLess } b pr2 = (*nhelper max record { x = x ; xLess = xLess2 } b (succInjective pr2)) +n b
    where
      xLess2 : x <N succ n
      xLess2 = PartialOrder.transitive (TotalOrder.order ℕTotalOrder) (a<SuccA x) xLess

  _*n_ : {n : ℕ} {pr : 0 <N n} → ℤn n pr → ℤn n pr → ℤn n pr
  _*n_ {0} {()}
  _*n_ {succ n} {_} record { x = a ; xLess = aLess } b = *nhelper a record { x = a ; xLess = aLess } b refl

  ℤnIdent : (n : ℕ) → (pr : 0 <N n) → ℤn n pr
  ℤnIdent 0 ()
  ℤnIdent 1 pr = record { x = 0 ; xLess = pr }
  ℤnIdent (succ (succ n)) _ = record { x = 1 ; xLess = succPreservesInequality (succIsPositive n) }

  ℤnMult0Right : {n : ℕ} {pr : 0 <N n} → (max : ℕ) → (a : ℤn n pr) → (modNToℕ a ≡ max) → (a *n record { x = 0 ; xLess = pr }) ≡ record { x = 0 ; xLess = pr }
  ℤnMult0Right {0} {()}
  ℤnMult0Right {succ n} .zero record { x = zero ; xLess = xLess } refl = equalityZn _ _ refl
  ℤnMult0Right {succ n} {pr} (.succ x) record { x = (succ x) ; xLess = xLess } refl rewrite ℤnMult0Right {succ n} {pr} x record { x = x ; xLess = PartialOrder.transitive (TotalOrder.order ℕTotalOrder) (a<SuccA x) xLess } refl = equalityZn _ _ refl

  ℤnMultCommutative : {n : ℕ} {pr : 0 <N n} → (a b : ℤn n pr) → (a *n b) ≡ (b *n a)
  ℤnMultCommutative {0} {()}
  ℤnMultCommutative {succ n} {pr} record { x = zero ; xLess = xLess } b with <NRefl pr xLess
  ... | refl rewrite ℤnMult0Right (modNToℕ b) b refl = equalityZn _ _ refl
  ℤnMultCommutative {succ n} record { x = (succ x) ; xLess = xLess } b = {!!}

  ℤnMultIdent : {n : ℕ} {pr : 0 <N n} → (a : ℤn n pr) → (ℤnIdent n pr) *n a ≡ a
  ℤnMultIdent {zero} {()}
  ℤnMultIdent {succ zero} {pr} record { x = zero ; xLess = (le diff proof) } = equalityZn _ _ refl
  ℤnMultIdent {succ zero} {pr} record { x = (succ a) ; xLess = (le diff proof) } = exFalso f
    where
      f : False
      f rewrite Semiring.commutative ℕSemiring diff (succ a) = naughtE (succInjective (equalityCommutative proof))
  ℤnMultIdent {succ (succ n)} {pr} record { x = a ; xLess = aLess } with orderIsTotal a (succ (succ n))
  ℤnMultIdent {succ (succ n)} {pr} record { x = a ; xLess = aLess } | inl (inl a<ssn) = equalityZn _ _ refl
  ℤnMultIdent {succ (succ n)} {pr} record { x = a ; xLess = aLess } | inl (inr ssn<a) = exFalso (PartialOrder.irreflexive (TotalOrder.order ℕTotalOrder) (PartialOrder.transitive (TotalOrder.order ℕTotalOrder) aLess ssn<a))
  ℤnMultIdent {succ (succ n)} {pr} record { x = .(succ (succ n)) ; xLess = aLess } | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order ℕTotalOrder) aLess)

  ℤnRing : (n : ℕ) → (pr : 0 <N n) → Ring (reflSetoid (ℤn n pr)) (_+n_) (_*n_)
  Ring.additiveGroup (ℤnRing n 0<n) = (ℤnGroup n 0<n)
  Ring.multWellDefined (ℤnRing n 0<n) = reflGroupWellDefined
  Ring.1R (ℤnRing n pr) = ℤnIdent n pr
  Ring.groupIsAbelian (ℤnRing n 0<n) = AbelianGroup.commutative (ℤnAbGroup n 0<n)
  Ring.multAssoc (ℤnRing n 0<n) = {!!}
  Ring.multCommutative (ℤnRing n 0<n) {a} {b} = ℤnMultCommutative a b
  Ring.multDistributes (ℤnRing n 0<n) = {!!}
  Ring.multIdentIsIdent (ℤnRing n 0<n) {a} = ℤnMultIdent a
