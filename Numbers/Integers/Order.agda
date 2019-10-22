{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Integers.Definition
open import Numbers.Integers.Addition
open import Numbers.Integers.Multiplication
open import Semirings.Definition
open import Rings.Definition
open import Rings.Order
open import Setoids.Setoids
open import Setoids.Orders
open import Orders

module Numbers.Integers.Order where

infix 5 _<Z_
record _<Z_ (a : ℤ) (b : ℤ) : Set where
  constructor le
  field
    x : ℕ
    proof : (nonneg (succ x)) +Z a ≡ b

lessLemma : (a x : ℕ) → succ x +N a ≡ a → False
lessLemma zero x pr = naughtE (equalityCommutative pr)
lessLemma (succ a) x pr = lessLemma a x q
  where
    q : succ x +N a ≡ a
    q rewrite Semiring.commutative ℕSemiring a (succ x) | Semiring.commutative ℕSemiring x a | Semiring.commutative ℕSemiring (succ a) x = succInjective pr

nonnegInjective : {a b : ℕ} → (nonneg a ≡ nonneg b) → (a ≡ b)
nonnegInjective {a} {.a} refl = refl

irreflexive : (x : ℤ) → x <Z x → False
irreflexive (nonneg x) record { x = y ; proof = proof } = lessLemma x y (nonnegInjective proof)
irreflexive (negSucc a) record { x = x ; proof = proof } = naughtE (equalityCommutative q)
  where
    pr' : nonneg (succ x) +Z (negSucc a +Z nonneg (succ a)) ≡ negSucc a +Z nonneg (succ a)
    pr' rewrite +ZAssociative (nonneg (succ x)) (negSucc a) (nonneg (succ a)) = applyEquality (λ t → t +Z nonneg (succ a)) proof
    pr'' : nonneg (succ x) +Z nonneg 0 ≡ nonneg 0
    pr'' rewrite equalityCommutative (additiveInverseExists a) = identityOfIndiscernablesLeft _≡_ pr' q
      where
        q : nonneg (succ x) +Z (negSucc a +Z nonneg (succ a)) ≡ nonneg (succ (x +N 0))
        q rewrite Semiring.commutative ℕSemiring x 0 | additiveInverseExists a | Semiring.commutative ℕSemiring x 0 = refl
    pr''' : succ x +N 0 ≡ 0
    pr''' = nonnegInjective pr''
    q : succ x ≡ 0
    q rewrite Semiring.commutative ℕSemiring 0 (succ x) = pr'''

lessZTransitive : {a b c : ℤ} → (a <Z b) → (b <Z c) → (a <Z c)
lessZTransitive {a} {b} {c} (le d1 pr1) (le d2 pr2) rewrite equalityCommutative pr1 = le (d1 +N succ d2) pr
  where
    pr : nonneg (succ (d1 +N succ d2)) +Z a ≡ c
    pr rewrite +ZAssociative (nonneg (succ d2)) (nonneg (succ d1)) a | Semiring.commutative ℕSemiring (succ d2) (succ d1) = pr2

lessInherits : {a b : ℕ} → (a <N b) → ((nonneg a) <Z (nonneg b))
_<Z_.x (lessInherits {a} {b} (le x proof)) = x
_<Z_.proof (lessInherits {a} {.(succ (x +N a))} (le x refl)) = refl

lessInheritsNegsucc : {a b : ℕ} → (a <N b) → ((negSucc b) <Z negSucc a)
_<Z_.x (lessInheritsNegsucc {a} {b} (le x proof)) = x
_<Z_.proof (lessInheritsNegsucc {a} {b} (le x proof)) rewrite equalityCommutative proof = transitivity (transitivity (+ZCommutative (nonneg x) (negSucc (x +N a))) (applyEquality (λ i → negSucc i +Z nonneg x) (Semiring.commutative ℕSemiring x a))) (equalityCommutative (negSucc+Nonneg a x))

lessNegsuccNonneg : {a b : ℕ} → (negSucc a <Z nonneg b)
_<Z_.x (lessNegsuccNonneg {a} {b}) = a +N b
_<Z_.proof (lessNegsuccNonneg {zero} {b}) = refl
_<Z_.proof (lessNegsuccNonneg {succ a} {b}) = _<Z_.proof (lessNegsuccNonneg {a} {b})

lessThanTotalZ : {a b : ℤ} → ((a <Z b) || (b <Z a)) || (a ≡ b)
lessThanTotalZ {nonneg a} {nonneg b} with orderIsTotal a b
lessThanTotalZ {nonneg a} {nonneg b} | inl (inl a<b) = inl (inl (lessInherits a<b))
lessThanTotalZ {nonneg a} {nonneg b} | inl (inr b<a) = inl (inr (lessInherits b<a))
lessThanTotalZ {nonneg a} {nonneg b} | inr a=b = inr (applyEquality nonneg a=b)
lessThanTotalZ {nonneg a} {negSucc b} = inl (inr (lessNegsuccNonneg {b} {a}))
lessThanTotalZ {negSucc a} {nonneg x} = inl (inl (lessNegsuccNonneg {a} {x}))
lessThanTotalZ {negSucc a} {negSucc b} with orderIsTotal a b
... | inl (inl a<b) = inl (inr (lessInheritsNegsucc a<b))
... | inl (inr b<a) = inl (inl (lessInheritsNegsucc b<a))
lessThanTotalZ {negSucc a} {negSucc .a} | inr refl = inr refl

ℤOrder : TotalOrder ℤ
PartialOrder._<_ (TotalOrder.order ℤOrder) = _<Z_
PartialOrder.irreflexive (TotalOrder.order ℤOrder) {a} = irreflexive a
PartialOrder.transitive (TotalOrder.order ℤOrder) = lessZTransitive
TotalOrder.totality ℤOrder a b = lessThanTotalZ {a} {b}

orderRespectsAddition : (a b : ℤ) → a <Z b → (c : ℤ) → a +Z c <Z b +Z c
orderRespectsAddition (nonneg a) (nonneg b) (le x proof) (nonneg c) = le x (transitivity (+ZAssociative (nonneg (succ x)) (nonneg a) (nonneg c)) (applyEquality (_+Z nonneg c) proof))
orderRespectsAddition (nonneg a) (nonneg b) (le x proof) (negSucc c) = le x (transitivity (+ZAssociative (nonneg (succ x)) (nonneg a) (negSucc c)) (applyEquality (_+Z negSucc c) proof))
orderRespectsAddition (negSucc a) (nonneg b) (le x proof) (nonneg c) = le x (transitivity (+ZAssociative (nonneg (succ x)) (negSucc a) (nonneg c)) (applyEquality (_+Z nonneg c) proof))
orderRespectsAddition (negSucc a) (nonneg b) (le x proof) (negSucc c) = le x (transitivity (+ZAssociative (nonneg (succ x)) (negSucc a) (negSucc c)) (applyEquality (_+Z negSucc c) proof))
orderRespectsAddition (negSucc a) (negSucc b) (le x proof) (nonneg c) = le x (transitivity (+ZAssociative (nonneg (succ x)) (negSucc a) (nonneg c)) (applyEquality (_+Z nonneg c) proof))
orderRespectsAddition (negSucc a) (negSucc b) (le x proof) (negSucc c) = le x (transitivity (+ZAssociative (nonneg (succ x)) (negSucc a) (negSucc c)) (applyEquality (_+Z negSucc c) proof))

orderRespectsMultiplication : (a b : ℤ) → nonneg 0 <Z a → nonneg 0 <Z b → nonneg 0 <Z a *Z b
orderRespectsMultiplication (nonneg (succ a)) (nonneg (succ b)) 0<a 0<b = lessInherits (succIsPositive (b +N a *N succ b))

ℤOrderedRing : OrderedRing ℤRing (totalOrderToSetoidTotalOrder ℤOrder)
OrderedRing.orderRespectsAddition ℤOrderedRing {a} {b} = orderRespectsAddition a b
OrderedRing.orderRespectsMultiplication ℤOrderedRing {a} {b} = orderRespectsMultiplication a b
