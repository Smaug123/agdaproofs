{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Groups.Groups
open import Groups.Abelian.Definition
open import Groups.FiniteGroups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Numbers.Naturals.Naturals
open import Setoids.Setoids
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Sets.Cardinality.Finite.Definition
open import Functions
open import Semirings.Definition
open import Numbers.Modulo.Definition
open import Numbers.Modulo.Addition
open import Orders.Total.Definition
open import Numbers.Naturals.EuclideanAlgorithm
open import Numbers.Modulo.ModuloFunction

module Numbers.Modulo.Group where

open TotalOrder ℕTotalOrder
open Semiring ℕSemiring

private
  0<s : {n : ℕ} → 0 <N succ n
  0<s {n} = le n (applyEquality succ (Semiring.sumZeroRight ℕSemiring n))

  inverseN : {n : ℕ} → .(0<n : 0 <N n) → (x : ℤn n 0<n) → ℤn n 0<n
  inverseN 0<n record { x = 0 ; xLess = _ } = record { x = 0 ; xLess = 0<n }
  inverseN 0<n record { x = succ x ; xLess = xLess } with <NProp xLess
  ... | le subtr pr = record { x = succ subtr ; xLess = le x (transitivity (commutative (succ x) (succ subtr)) pr) }

  invLeft : {n : ℕ} → .(0<n : 0 <N n) → (x : ℤn n 0<n) → _+n_ 0<n (inverseN 0<n x) x ≡ record { x = 0 ; xLess = 0<n }
  invLeft {n} 0<n record { x = 0 ; xLess = xLess } = plusZnIdentityLeft 0<n (record { x = 0 ; xLess = 0<n })
  invLeft {n} 0<n record { x = (succ x) ; xLess = xLess } with <NProp xLess
  ... | le subtr pr rewrite pr = equalityZn (modN 0<n)

ℤnGroup : (n : ℕ) → .(pr : 0 <N n) → Group (reflSetoid (ℤn n pr)) (_+n_ pr)
Group.+WellDefined (ℤnGroup n 0<n) refl refl = refl
Group.0G (ℤnGroup n 0<n) = record { x = 0 ; xLess = 0<n }
Group.inverse (ℤnGroup n 0<n) = inverseN 0<n
Group.+Associative (ℤnGroup n 0<n) {a} {b} {c} = equalityCommutative (plusZnAssociative 0<n a b c)
Group.identRight (ℤnGroup n 0<n) {a} = plusZnIdentityRight 0<n a
Group.identLeft (ℤnGroup n 0<n) {a} = plusZnIdentityLeft 0<n a
Group.invLeft (ℤnGroup n 0<n) {a} = invLeft 0<n a
Group.invRight (ℤnGroup n 0<n) {a} = transitivity (plusZnCommutative 0<n a (inverseN 0<n a)) (invLeft 0<n a)

ℤnAbGroup : (n : ℕ) → (pr : 0 <N n) → AbelianGroup (ℤnGroup n pr)
AbelianGroup.commutative (ℤnAbGroup n pr) {a} {b} = plusZnCommutative pr a b

ℤnFinite : (n : ℕ) → (pr : 0 <N n) → FiniteGroup (ℤnGroup n pr) (FinSet n)
SetoidToSet.project (FiniteGroup.toSet (ℤnFinite (succ n) 0<n)) record { x = x ; xLess = xLess } = ofNat x xLess
SetoidToSet.wellDefined (FiniteGroup.toSet (ℤnFinite (succ n) 0<n)) x y x=y rewrite x=y = refl
SetoidToSet.surj (FiniteGroup.toSet (ℤnFinite (succ n) 0<n)) b = record { x = toNat b ; xLess = toNatSmaller b } , ofNatToNat b
SetoidToSet.inj (FiniteGroup.toSet (ℤnFinite (succ n) 0<n)) record { x = x ; xLess = xLess } record { x = y ; xLess = yLess } eq = equalityZn (ofNatInjective x y xLess yLess eq)
FiniteGroup.finite (ℤnFinite n pr) = record { size = n ; mapping = id ; bij = idIsBijective }
