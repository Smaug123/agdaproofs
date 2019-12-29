{-# OPTIONS --safe --warning=error #-}
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
open import Numbers.Primes.PrimeNumbers
open import Setoids.Setoids
open import Sets.FinSet
open import Sets.FinSetWithK
open import Functions
open import Numbers.Naturals.WithK
open import Semirings.Definition
open import Orders.Total.Definition
open import Numbers.Modulo.Definition

module Numbers.Modulo.Addition where
open TotalOrder ℕTotalOrder

cancelSumFromInequality : {a b c : ℕ} → a +N b <N a +N c → b <N c
cancelSumFromInequality {a} {b} {c} (le x proof) = le x help
  where
    help : succ x +N b ≡ c
    help rewrite Semiring.+Associative ℕSemiring (succ x) a b | Semiring.commutative ℕSemiring x a | equalityCommutative (Semiring.+Associative ℕSemiring (succ a) x b) | Semiring.commutative ℕSemiring a (x +N b) | Semiring.commutative ℕSemiring (succ (x +N b)) a = canSubtractFromEqualityLeft {a} proof

_+n_ : {n : ℕ} {pr : 0 <N n} → ℤn n pr → ℤn n pr → ℤn n pr
_+n_ {0} {le x ()} a b
_+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } with totality (a +N b) (succ n)
_+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl (a+b<n)) = record { x = a +N b ; xLess = a+b<n }
_+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr (n<a+b)) = record { x = subtractionNResult.result sub ; xLess = pr2 }
    where
      sub : subtractionNResult (succ n) (a +N b) (inl n<a+b)
      sub = -N (inl n<a+b)
      pr1 : a +N b <N succ n +N succ n
      pr1 = addStrongInequalities aLess bLess
      pr1' : succ n +N (subtractionNResult.result sub) <N succ n +N succ n
      pr1' rewrite subtractionNResult.pr sub = pr1
      pr2 : subtractionNResult.result sub <N succ n
      pr2 = cancelSumFromInequality pr1'
_+n_ {succ n} {pr} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr (a+b=n) = record { x = 0 ; xLess = succIsPositive n }

plusZnIdentityRight : {n : ℕ} → {pr : 0 <N n} → (a : ℤn n pr) → (a +n record { x = 0 ; xLess = pr }) ≡ a
plusZnIdentityRight {zero} {()} a
plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } with totality (a +N 0) (succ x)
plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } | inl (inl a<sx) = equalityZn _ _ (Semiring.commutative ℕSemiring a 0)
plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } | inl (inr sx<a) = exFalso (f aLess sx<a)
  where
    f : (aL : a <N succ x) → (sx<a : succ x <N a +N 0) → False
    f aL sx<a rewrite Semiring.commutative ℕSemiring a 0 = irreflexive (<Transitive aL sx<a)
plusZnIdentityRight {succ x} {_} record { x = a ; xLess = aLess } | inr a=sx = exFalso (f aLess a=sx)
  where
    f : (aL : a <N succ x) → (a=sx : a +N 0 ≡ succ x) → False
    f aL a=sx rewrite Semiring.commutative ℕSemiring a 0 | a=sx = TotalOrder.irreflexive ℕTotalOrder aL


plusZnIdentityLeft : {n : ℕ} → {pr : 0 <N n} → (a : ℤn n pr) → (record { x = 0 ; xLess = pr }) +n a ≡ a
plusZnIdentityLeft {zero} {()}
plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } with totality x (succ n)
plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } | inl (inl x<succn) rewrite <NRefl x<succn xLess = refl
plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } | inl (inr succn<x) = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder succn<x xLess))
plusZnIdentityLeft {succ n} {pr} record { x = x ; xLess = xLess } | inr x=succn rewrite x=succn = exFalso (TotalOrder.irreflexive ℕTotalOrder xLess)

subLemma : {a b c : ℕ} → (pr1 : a <N b) → (pr2 : a <N c) → (pr : b ≡ c) → (subtractionNResult.result (-N (inl pr1))) ≡ (subtractionNResult.result (-N (inl pr2)))
subLemma {a} {b} {c} a<b a<c b=c rewrite b=c | <NRefl a<b a<c = refl

plusZnCommutative : {n : ℕ} → {pr : 0 <N n} → (a b : ℤn n pr) → (a +n b) ≡ b +n a
plusZnCommutative {zero} {()} a b
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } with totality (a +N b) (succ n)
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) with totality (b +N a) (succ n)
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) | inl (inl b+a<sn) = equalityZn _ _ (Semiring.commutative ℕSemiring a b)
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) | inl (inr sn<b+a) = exFalso (f a+b<sn sn<b+a)
  where
    f : (a +N b) <N succ n → succ n <N b +N a → False
    f pr1 pr2 rewrite Semiring.commutative ℕSemiring b a = TotalOrder.irreflexive ℕTotalOrder (<Transitive pr2 pr1)
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inl a+b<sn) | inr b+a=sn = exFalso (f a+b<sn b+a=sn)
  where
    f : (a +N b) <N succ n → b +N a ≡ succ n → False
    f pr1 eq rewrite Semiring.commutative ℕSemiring b a | eq = TotalOrder.irreflexive ℕTotalOrder pr1
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) with totality (b +N a) (succ n)
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) | inl (inl b+a<sn) = exFalso (f sn<a+b b+a<sn)
  where
    f : succ n <N a +N b → b +N a <N succ n → False
    f pr1 pr2 rewrite Semiring.commutative ℕSemiring b a = TotalOrder.irreflexive ℕTotalOrder (<Transitive sn<a+b b+a<sn)
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) | inl (inr sn<b+a) = equalityZn _ _ (subLemma sn<a+b sn<b+a (Semiring.commutative ℕSemiring a b))
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inl (inr sn<a+b) | inr sn=b+a = exFalso (f sn<a+b sn=b+a)
  where
    f : succ n <N a +N b → b +N a ≡ succ n → False
    f pr eq rewrite Semiring.commutative ℕSemiring b a | eq = TotalOrder.irreflexive ℕTotalOrder pr
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b with totality (b +N a) (succ n)
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b | inl (inl b+a<sn) = exFalso f
  where
    f : False
    f rewrite Semiring.commutative ℕSemiring b a | sn=a+b = TotalOrder.irreflexive ℕTotalOrder b+a<sn
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b | inl (inr sn<b+a) = exFalso f
  where
    f : False
    f rewrite Semiring.commutative ℕSemiring b a | sn=a+b = TotalOrder.irreflexive ℕTotalOrder sn<b+a
plusZnCommutative {succ n} {_} record { x = a ; xLess = aLess } record { x = b ; xLess = bLess } | inr sn=a+b | inr sn=b+a = equalityZn _ _ refl
