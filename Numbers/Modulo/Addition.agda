{-# OPTIONS --safe --warning=error --without-K #-}
-- These are explicitly with-K, because we currently encode an element of Zn as
-- a natural together with a proof that it is small.

open import LogicalFormulae
open import Groups.Definition
open import Groups.Groups
open import Groups.Abelian.Definition
open import Groups.FiniteGroups.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Setoids.Setoids
open import Sets.FinSet.Definition
open import Functions
open import Semirings.Definition
open import Orders.Total.Definition
open import Numbers.Modulo.Definition
open import Numbers.Modulo.ModuloFunction
open import Numbers.Naturals.Order.Lemmas

module Numbers.Modulo.Addition where
open TotalOrder ℕTotalOrder

_+n_ : {n : ℕ} .(pr : 0 <N n) → ℤn n pr → ℤn n pr → ℤn n pr
_+n_ {n} pr a b = record { x = mod n pr (ℤn.x a +N ℤn.x b) ; xLess = mod<N pr _ }

plusZnIdentityRight : {n : ℕ} → .(pr : 0 <N n) → (a : ℤn n pr) → (_+n_ pr a record { x = 0 ; xLess = pr }) ≡ a
plusZnIdentityRight 0<n record { x = x ; xLess = xLess } rewrite Semiring.sumZeroRight ℕSemiring x = equalityZn (modIsMod 0<n x (<NProp xLess))

plusZnIdentityLeft : {n : ℕ} → .(pr : 0 <N n) → (a : ℤn n pr) → _+n_ pr (record { x = 0 ; xLess = pr }) a ≡ a
plusZnIdentityLeft 0<n record { x = x ; xLess = xLess } = equalityZn (modIsMod 0<n x (<NProp xLess))

plusZnCommutative : {n : ℕ} → .(pr : 0 <N n) → (a b : ℤn n pr) → _+n_ pr a b ≡ _+n_ pr b a
plusZnCommutative {n} 0<n a b = equalityZn (applyEquality (mod n 0<n) (Semiring.commutative ℕSemiring (ℤn.x a) _))

plusZnAssociative' : {n : ℕ} → .(pr : 0 <N n) → {a b c : ℕ} → (a <N n) → (b <N n) → (c <N n) → mod n pr ((mod n pr (a +N b)) +N c) ≡ mod n pr (a +N (mod n pr (b +N c)))
plusZnAssociative' 0<n {a} {b} {c} a<n b<n c<n with modAddition 0<n a<n b<n
plusZnAssociative' {n} 0<n {a} {b} {c} a<n b<n c<n | inl a+b=mod with modAddition 0<n b<n c<n
... | inl b+c=mod rewrite equalityCommutative (a+b=mod) | equalityCommutative (b+c=mod) = applyEquality (mod _ 0<n) (equalityCommutative (Semiring.+Associative ℕSemiring a b c))
... | inr b+c=n+mod rewrite equalityCommutative (a+b=mod) | equalityCommutative (modAnd+n 0<n (a +N mod _ 0<n (b +N c))) | Semiring.+Associative ℕSemiring n a (mod _ 0<n (b +N c)) | Semiring.commutative ℕSemiring n a | equalityCommutative (Semiring.+Associative ℕSemiring a n (mod _ 0<n (b +N c))) | equalityCommutative b+c=n+mod = applyEquality (mod _ 0<n) (equalityCommutative (Semiring.+Associative ℕSemiring a b c))
plusZnAssociative' 0<n {a} {b} {c} a<n b<n c<n | inr a+b=n+mod with modAddition 0<n b<n c<n
plusZnAssociative' {n} 0<n {a} {b} {c} a<n b<n c<n | inr a+b=n+mod | inl b+c=mod rewrite equalityCommutative b+c=mod | equalityCommutative (modAnd+n 0<n (mod _ 0<n (a +N b) +N c)) | Semiring.+Associative ℕSemiring n (mod _ 0<n (a +N b)) c | equalityCommutative a+b=n+mod = applyEquality (mod _ 0<n) (equalityCommutative (Semiring.+Associative ℕSemiring a b c))
plusZnAssociative' {n} 0<n {a} {b} {c} a<n b<n c<n | inr a+b=n+mod | inr b+c=n+mod rewrite equalityCommutative (modAnd+n 0<n ((mod _ 0<n (a +N b)) +N c)) | equalityCommutative (modAnd+n 0<n (a +N mod _ 0<n (b +N c))) | Semiring.+Associative ℕSemiring n (mod _ 0<n (a +N b)) c | equalityCommutative (a+b=n+mod) | Semiring.commutative ℕSemiring a (mod n 0<n (b +N c)) | Semiring.+Associative ℕSemiring n (mod n 0<n (b +N c)) a | equalityCommutative b+c=n+mod | Semiring.commutative ℕSemiring (b +N c) a = applyEquality (mod _ 0<n) (equalityCommutative (Semiring.+Associative ℕSemiring a b c))

plusZnAssociative : {n : ℕ} → .(pr : 0 <N n) → (a b c : ℤn n pr) → _+n_ pr (_+n_ pr a b) c ≡ _+n_ pr a (_+n_ pr b c)
plusZnAssociative {succ n} 0<sn record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } record { x = c ; xLess = cLess } = equalityZn t
  where
    ma = mod (succ n) 0<sn a
    mb = mod (succ n) 0<sn b
    mc = mod (succ n) 0<sn c
    v : mod (succ n) 0<sn ((mod (succ n) 0<sn (ma +N mb)) +N mc) ≡ mod (succ n) 0<sn (ma +N mod (succ n) 0<sn (mb +N mc))
    v = plusZnAssociative' 0<sn (mod<N 0<sn a) (mod<N 0<sn b) (mod<N 0<sn c)
    u : mod (succ n) 0<sn ((mod (succ n) 0<sn (mod (succ n) 0<sn a +N (mod (succ n) 0<sn b))) +N c) ≡ mod (succ n) 0<sn (a +N mod (succ n) 0<sn ((mod (succ n) 0<sn b) +N (mod (succ n) 0<sn c)))
    u rewrite equalityCommutative (modIsMod 0<sn c (<NProp cLess)) | equalityCommutative (modIsMod 0<sn a (<NProp aLess)) | modIdempotent 0<sn a | modIdempotent 0<sn c = v
    t : mod (succ n) 0<sn (mod (succ n) 0<sn (a +N b) +N c) ≡ mod (succ n) 0<sn (a +N mod (succ n) 0<sn (b +N c))
    t rewrite modExtracts {succ n} 0<sn a b | modExtracts {succ n} 0<sn b c = u
