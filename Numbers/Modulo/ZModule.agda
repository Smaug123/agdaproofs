{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Definition
open import Groups.Abelian.Definition
open import Groups.FiniteGroups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Setoids.Setoids
open import Sets.FinSet.Definition
open import Sets.FinSet.Lemmas
open import Functions
open import Semirings.Definition
open import Numbers.Modulo.Definition
open import Numbers.Modulo.Addition
open import Orders.Total.Definition
open import Numbers.Modulo.ModuloFunction
open import Numbers.Integers.Definition
open import Numbers.Modulo.Group
open import Modules.Definition
open import Numbers.Integers.RingStructure.Ring

module Numbers.Modulo.ZModule {n : ℕ} (pr : 0 <N n) where

timesNat : ℕ → ℤn n pr → ℤn n pr
timesNat 0 b = record { x = 0 ; xLess = pr }
timesNat (succ x) b = _+n_ pr b (timesNat x b)

times : ℤ → ℤn n pr → ℤn n pr
times (nonneg x) b = timesNat x b
times (negSucc x) b = Group.inverse (ℤnGroup n pr) (timesNat (succ x) b)

dotDistributesLeft : (r : ℤ) → (x y : ℤn n pr) → times r ((_ +n x) y) ≡ (_ +n times r x) (times r y)
dotDistributesLeft (nonneg zero) x y = equalityCommutative (Group.identRight (ℤnGroup n pr))
dotDistributesLeft (nonneg (succ r)) x y rewrite dotDistributesLeft (nonneg r) x y = equalityZn (transitivity (equalityCommutative (modExtracts pr _ _)) (transitivity (applyEquality (mod n pr) (transitivity (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring (ℤn.x x) _ _)) (applyEquality (ℤn.x x +N_) (transitivity (Semiring.commutative ℕSemiring (ℤn.x y) _) (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring _ (ℤn.x (timesNat r y)) (ℤn.x y))) (applyEquality (ℤn.x (timesNat r x) +N_) (Semiring.commutative ℕSemiring (ℤn.x (timesNat r y)) (ℤn.x y))))))) (Semiring.+Associative ℕSemiring (ℤn.x x) _ _))) (modExtracts pr _ _)))
dotDistributesLeft (negSucc r) x y = {!!}

ZnZModule : Module ℤRing (ℤnAbGroup n pr) times
Module.dotWellDefined (ZnZModule) refl refl = refl
Module.dotDistributesLeft (ZnZModule) {r} {x} {y} = dotDistributesLeft r x y
Module.dotDistributesRight (ZnZModule) = {!!}
Module.dotAssociative (ZnZModule) = {!!}
Module.dotIdentity (ZnZModule) {record { x = x ; xLess = xLess }} = {!!}
