{-# OPTIONS --warning=error --safe --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Numbers.Integers.Integers
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Subtraction
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Numbers.Naturals.Exponentiation
open import Numbers.Primes.PrimeNumbers
open import Maybe
open import Semirings.Definition
open import Numbers.Naturals.EuclideanAlgorithm
open import Sequences
open import Vectors

module LectureNotes.NumbersAndSets.Examples1 where

open Semiring ℕSemiring
open import Semirings.Solver ℕSemiring multiplicationNIsCommutative

private
  abstract
    q1Lemma1 : {q r : ℕ} → 3 *N succ q +N r ≡ succ (succ (succ (3 *N q +N r)))
    q1Lemma1 {q} {r} rewrite sumZeroRight q | commutative q (succ q) | commutative q (succ (succ (q +N q))) | +Associative q q q = refl

    q1Lemma : {n : ℕ} → (2 <N n) → ((3 ∣ n) || (3 ∣ (n +N 2))) || (3 ∣ (n +N 4))
    q1Lemma {zero} ()
    q1Lemma {succ zero} (le zero ())
    q1Lemma {succ zero} (le (succ x) ())
    q1Lemma {succ (succ zero)} (le (succ x) proof) rewrite Semiring.commutative ℕSemiring x 2 = exFalso (naughtE (equalityCommutative (succInjective (succInjective proof))))
    q1Lemma {succ (succ (succ zero))} 2<n = inl (inl (aDivA 3))
    q1Lemma {succ (succ (succ (succ zero)))} 2<n = inl (inr (divides (record { quot = 2 ; rem = zero ; pr = refl ; remIsSmall = inl (le 2 refl) ; quotSmall = inl (le 2 refl)}) refl))
    q1Lemma {succ (succ (succ (succ (succ zero))))} 2<n = inr (divides (record { quot = 3 ; rem = zero ; pr = refl ; remIsSmall = inl (le 2 refl) ; quotSmall = inl (le 2 refl)}) refl)
    q1Lemma {succ (succ (succ (succ (succ (succ n)))))} 2<n with q1Lemma {succ (succ (succ n))} (le n (applyEquality succ (Semiring.commutative ℕSemiring n 2)))
    q1Lemma {succ (succ (succ (succ (succ (succ n)))))} 2<n | inl (inl (divides record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } x)) = inl (inl (divides (record { quot = succ quot ; rem = rem ; pr = transitivity (q1Lemma1 {quot} {rem}) (applyEquality (λ x → succ (succ (succ x))) pr) ; remIsSmall = remIsSmall ; quotSmall = inl (le 2 refl) }) x))
    q1Lemma {succ (succ (succ (succ (succ (succ n)))))} 2<n | inl (inr (divides record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } x)) = inl (inr (divides record { quot = succ quot ; rem = rem ; pr = transitivity (q1Lemma1 {quot} {rem}) (applyEquality (λ x → succ (succ (succ x))) pr) ; remIsSmall = remIsSmall ; quotSmall = inl (le 2 refl) } x))
    q1Lemma {succ (succ (succ (succ (succ (succ n)))))} 2<n | inr (divides record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } x) = inr (divides record { quot = succ quot ; rem = rem ; pr = transitivity (q1Lemma1 {quot} {rem}) (applyEquality (λ x → succ (succ (succ x))) pr) ; remIsSmall = remIsSmall ; quotSmall = inl (le 2 refl) } x)

q1 : {n : ℕ} → Prime n → Prime (n +N 2) → Prime (n +N 4) → n ≡ 3
q1 {succ zero} record { p>1 = (le zero ()) ; pr = pr } pN+2 pN+4
q1 {succ zero} record { p>1 = (le (succ x) ()) ; pr = pr } pN+2 pN+4
q1 {succ (succ zero)} pN record { p>1 = p>1 ; pr = pr } pN+4 with pr {2} (divides (record { quot = 2 ; rem = zero ; pr = refl ; remIsSmall = inl (le 1 refl) ; quotSmall = inl (le 1 refl)}) refl) (le 1 refl) (le 1 refl)
q1 {succ (succ zero)} pN record { p>1 = p>1 ; pr = pr } pN+4 | ()
q1 {succ (succ (succ n))} pN pN+2 pN+4 with q1Lemma {succ (succ (succ n))} (le n (applyEquality succ (commutative n 2)))
q1 {succ (succ (succ n))} pN pN+2 pN+4 | inl (inl 3|n) = equalityCommutative (primeDivPrimeImpliesEqual threeIsPrime pN 3|n)
q1 {succ (succ (succ n))} pN pN+2 pN+4 | inl (inr 3|n+2) with primeDivPrimeImpliesEqual threeIsPrime pN+2 3|n+2
... | bl rewrite commutative n 2 = exFalso (naughtE (succInjective (succInjective (succInjective bl))))
q1 {succ (succ (succ n))} pN pN+2 pN+4 | inr 3|n+4 with primeDivPrimeImpliesEqual threeIsPrime pN+4 3|n+4
... | bl rewrite commutative n 4 = exFalso (naughtE (succInjective (succInjective (succInjective bl))))

q3Differences : ℕ → ℕ
q3Differences a = 2 *N a
q3Seq : (start : ℕ) → ℕ → ℕ
q3Seq start zero = start
q3Seq start (succ n) = q3Differences (succ n) +N q3Seq start n
q3SeqFirst : take 5 (funcToSequence (q3Seq 41)) ≡ 41 ,- 43 ,- 47 ,- 53 ,- 61 ,- []
q3SeqFirst = refl
q3N : (start : ℕ) (a : ℕ) → q3Seq start a ≡ start +N (a +N (a *N a))
q3N start zero = equalityCommutative (sumZeroRight start)
q3N start (succ a) rewrite q3N start a | sumZeroRight a =
  from (succ (plus (plus (const a) (succ (const a))) (plus (const start) (plus (const a) (times (const a) (const a))))))
  to (plus (const start) (succ (plus (const a) (succ (plus (const a) (times (const a) (succ (const a))))))))
  by applyEquality (λ i → succ (succ i)) (transitivity (+Associative (a +N a) start _) (transitivity (transitivity (applyEquality (_+N (a +N a *N a)) (commutative (a +N a) start)) (equalityCommutative (+Associative start _ _))) (applyEquality (start +N_) (equalityCommutative (+Associative a a (a +N a *N a))))))
q3NDivision : (start : ℕ) → start ∣ (q3Seq start start)
q3NDivision 0 = aDivA 0
q3NDivision (succ start) rewrite q3N (succ start) (succ start) = dividesBothImpliesDividesSum {succ start} {succ start} (aDivA (succ start)) (dividesBothImpliesDividesSum {succ start} {succ start} (aDivA (succ start)) (divides (record { quot = succ start ; rem = 0 ; pr = sumZeroRight _ ; remIsSmall = inl (succIsPositive start) ; quotSmall = inl (succIsPositive start) }) refl))

q3 : (start : ℕ) → ((n : ℕ) → Prime (q3Seq start n)) → False
q3 zero a with a 2
... | record { p>1 = p>1 ; pr = pr } with pr {2} (divides (record { quot = 3 ; rem = 0 ; pr = refl ; remIsSmall = inl (le 1 refl) ; quotSmall = inl (le 1 refl) }) refl) (le 3 refl) (succIsPositive 1)
... | ()
q3 (succ zero) a with a 0
... | record { p>1 = le zero () ; pr = pr }
... | record { p>1 = le (succ x) () ; pr = pr }
q3 (succ (succ start)) a with q3NDivision (succ (succ start))
... | r with a (succ (succ start))
... | s = compositeImpliesNotPrime (succ (succ start)) _ (succPreservesInequality (succIsPositive start)) (le (succ (succ start) +N ((start +N succ start) +N q3Seq (succ (succ start)) start)) (applyEquality (λ i → succ (succ i)) (from (succ (plus (plus (const start) (plus (plus (const start) (succ (const start))) (const (q3Seq (succ (succ start)) start)))) (succ (succ (const start))))) to plus (plus (const start) (succ (succ (plus (const start) zero)))) (succ (plus (plus (const start) (succ (plus (const start) zero))) (const (q3Seq (succ (succ start)) start)))) by applyEquality (λ i → succ (succ (succ (succ i)))) (transitivity (commutative _ start) (+Associative start start _))))) r s

q3' : ((n : ℕ) → Prime (q3Seq 41 n)) → False
q3' = q3 41

q6 : {n : ℕ} → 3 ∣ (n *N n) → 3 ∣ n
q6 {n} 3|n^2 with primesArePrime {3} {n} {n} threeIsPrime 3|n^2
q6 {n} 3|n^2 | inl x = x
q6 {n} 3|n^2 | inr x = x

_*q10_ : {a : ℕ} → {b : ℕ} → (0 <N a) → (0 <N b) → ℕ
*q10Pos : {a : ℕ} → {b : ℕ} → (0<a : 0 <N a) → (0<b : 0 <N b) → 0 <N (_*q10_ 0<a 0<b)

_*q10_ {succ zero} {succ b} 0<a 0<b = succ (succ b)
_*q10_ {succ (succ a)} {succ zero} 0<a 0<b = _*q10_ {succ a} {2} (le a (applyEquality succ (sumZeroRight a))) (le 1 refl)
_*q10_ {succ (succ a)} {succ (succ b)} 0<a 0<b = _*q10_ {succ a} {_*q10_ {succ (succ a)} {succ b} 0<a (le b (applyEquality succ (sumZeroRight b)))} (le a (applyEquality succ (sumZeroRight a))) (*q10Pos 0<a (le b (applyEquality succ (sumZeroRight b))))
*q10Pos {succ zero} {succ b} 0<a 0<b = le (succ b) (applyEquality (λ i → succ (succ i)) (sumZeroRight b))
*q10Pos {succ (succ a)} {succ zero} 0<a 0<b = *q10Pos (le a (applyEquality succ (sumZeroRight a))) (le 1 refl)
*q10Pos {succ (succ a)} {succ (succ b)} 0<a 0<b = *q10Pos (le a (applyEquality succ (sumZeroRight a))) (*q10Pos 0<a (le b (applyEquality succ (sumZeroRight b))))
