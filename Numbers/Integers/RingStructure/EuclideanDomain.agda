{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Multiplication
open import Numbers.Integers.Order
open import Numbers.Integers.RingStructure.Ring
open import Numbers.Integers.RingStructure.IntegralDomain
open import Semirings.Definition
open import Groups.Definition
open import Rings.Definition
open import Setoids.Setoids
open import Rings.EuclideanDomains.Definition
open import Orders
open import Numbers.Naturals.EuclideanAlgorithm

module Numbers.Integers.RingStructure.EuclideanDomain where

private
  norm : ℤ → ℕ
  norm (nonneg x) = x
  norm (negSucc x) = succ x

  norm' : {a : ℤ} → (a!=0 : (a ≡ nonneg 0) → False) → ℕ
  norm' {a} _ = norm a

  multiplyIncreasesSuccLemma : (a b : ℕ) → succ (succ a) <N (succ (succ a)) *N (succ (succ b))
  multiplyIncreasesSuccLemma a b with multiplyIncreases (succ (succ b)) (succ (succ a)) (le b (applyEquality succ (Semiring.commutative ℕSemiring b 1))) (le (succ a) (applyEquality (λ i → succ (succ i)) (Semiring.sumZeroRight ℕSemiring a)))
  ... | bl rewrite multiplicationNIsCommutative (succ (succ b)) (succ (succ a)) = bl

  multiplyIncreasesSucc : (a b : ℕ) → succ a ≤N (succ a) *N (succ b)
  multiplyIncreasesSucc zero zero = inr refl
  multiplyIncreasesSucc zero (succ b) = inl (le (b +N 0) (Semiring.commutative ℕSemiring (succ (b +N 0)) 1))
  multiplyIncreasesSucc (succ a) zero = inr (applyEquality (λ i → succ (succ i)) (equalityCommutative (productWithOneRight a)))
  multiplyIncreasesSucc (succ a) (succ b) = inl (multiplyIncreasesSuccLemma a b)

  multiplyIncreasesSuccLemma' : (a b : ℕ) → succ (succ a) <N succ ((succ (succ a)) *N succ b) +N succ a
  multiplyIncreasesSuccLemma' a b = succPreservesInequality (le (b +N succ (b +N a *N succ b)) refl)

  multiplyIncreasesSucc' : (a b : ℕ) → succ a ≤N succ ((b +N a *N b) +N a)
  multiplyIncreasesSucc' zero zero = inr refl
  multiplyIncreasesSucc' zero (succ b) = inl (le b (applyEquality succ (transitivity (Semiring.commutative ℕSemiring b 1) (transitivity (equalityCommutative (Semiring.sumZeroRight ℕSemiring (succ b))) (equalityCommutative (Semiring.sumZeroRight ℕSemiring _))))))
  multiplyIncreasesSucc' (succ a) zero rewrite multiplicationNIsCommutative a zero = inr refl
  multiplyIncreasesSucc' (succ a) (succ b) = inl (multiplyIncreasesSuccLemma' a b)

  normSize : {a b : ℤ} → (a!=0 : (a ≡ nonneg 0) → False) → (b!=0 : (b ≡ nonneg 0) → False) → (c : ℤ) → b ≡ (a *Z c) → (norm a) ≤N (norm b)
  normSize {nonneg a} {nonneg b} a!=0 b!=0 (nonneg zero) b=ac rewrite nonnegInjective b=ac | multiplicationNIsCommutative a 0 = exFalso (b!=0 refl)
  normSize {nonneg a} {nonneg b} a!=0 b!=0 (nonneg (succ 0)) b=ac rewrite nonnegInjective b=ac | multiplicationNIsCommutative a 1 = inr (equalityCommutative (Semiring.sumZeroRight ℕSemiring a))
  normSize {nonneg 0} {nonneg b} a!=0 b!=0 (nonneg (succ (succ c))) b=ac = exFalso (a!=0 refl)
  normSize {nonneg (succ a)} {nonneg (succ b)} a!=0 b!=0 (nonneg (succ (succ c))) b=ac rewrite nonnegInjective b=ac = multiplyIncreasesSucc a (succ c)
  normSize {nonneg 0} {nonneg b} a!=0 b!=0 (negSucc c) bad = exFalso (a!=0 refl)
  normSize {nonneg (succ a)} {nonneg b} a!=0 b!=0 (negSucc c) ()
  normSize {nonneg a} {negSucc b} a!=0 b!=0 (nonneg c) ()
  normSize {nonneg (succ a)} {negSucc b} a!=0 b!=0 (negSucc c) pr rewrite negSuccInjective pr = multiplyIncreasesSucc' a c
  normSize {negSucc a} {nonneg zero} _ b!=0 c pr = exFalso (b!=0 refl)
  normSize {negSucc a} {nonneg (succ b)} _ _ (nonneg zero) ()
  normSize {negSucc a} {nonneg (succ b)} _ _ (nonneg (succ x)) ()
  normSize {negSucc a} {nonneg (succ b)} _ _ (negSucc c) pr rewrite nonnegInjective pr = multiplyIncreasesSucc a c
  normSize {negSucc a} {negSucc b} _ _ (nonneg (succ c)) pr rewrite negSuccInjective pr | multiplicationNIsCommutative c a | Semiring.commutative ℕSemiring (a +N a *N c) c | Semiring.+Associative ℕSemiring c a (a *N c) | Semiring.commutative ℕSemiring c a | equalityCommutative (Semiring.+Associative ℕSemiring a c (a *N c)) | Semiring.commutative ℕSemiring a (c +N a *N c) = multiplyIncreasesSucc' a c

  divAlg : {a b : ℤ} → (a!=0 : (a ≡ nonneg 0) → False) → (b!=0 : (b ≡ nonneg 0) → False) → DivisionAlgorithmResult ℤRing norm' a!=0 b!=0
  divAlg {nonneg zero} {b} a!=0 b!=0 = exFalso (a!=0 refl)
  divAlg {nonneg (succ a)} {nonneg zero} a!=0 b!=0 = exFalso (b!=0 refl)
  divAlg {nonneg (succ a)} {nonneg (succ b)} a!=0 b!=0 with divisionAlg (succ b) (succ a)
  divAlg {nonneg (succ a)} {nonneg (succ b)} a!=0 b!=0 | record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = record { quotient = nonneg quot ; rem = nonneg rem ; remSmall = u ; divAlg = transitivity (applyEquality nonneg (equalityCommutative pr)) t }
    where
      t : nonneg ((quot +N b *N quot) +N rem) ≡ nonneg (quot *N succ b) +Z nonneg rem
      t rewrite multiplicationNIsCommutative (succ b) quot = +Zinherits (quot *N succ b) rem
      u : (nonneg rem ≡ nonneg 0) || Sg ((nonneg rem ≡ nonneg 0) → False) (λ pr → rem <N succ b)
      u with TotalOrder.totality ℤOrder (nonneg 0) (nonneg rem)
      u | inl (inl 0<rem) = inr ((λ p → TotalOrder.irreflexive ℤOrder (TotalOrder.<WellDefined ℤOrder refl p 0<rem)) , remIsSmall)
      u | inr 0=rem rewrite 0=rem = inl refl
  divAlg {nonneg (succ a)} {negSucc b} _ _ with divisionAlg (succ b) (succ a)
  divAlg {nonneg (succ a)} {negSucc b} _ _ | record { quot = zero ; rem = rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = inl quotSmall } rewrite multiplicationNIsCommutative b 0 = record { quotient = nonneg 0 ; rem = nonneg rem ; remSmall = inr (p , remIsSmall) ; divAlg = applyEquality nonneg (equalityCommutative pr) }
    where
      p : (nonneg rem ≡ nonneg 0) → False
      p pr2 rewrite pr = naughtE (equalityCommutative (nonnegInjective pr2))
  divAlg {nonneg (succ a)} {negSucc b} _ _ | record { quot = succ quot ; rem = zero ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = inl quotSmall } = record { quotient = negSucc quot ; rem = nonneg zero ; remSmall = inl refl ; divAlg = applyEquality nonneg (transitivity (equalityCommutative pr) (applyEquality (λ i → i +N 0) (multiplicationNIsCommutative (succ b) (succ quot)))) }
  divAlg {nonneg (succ a)} {negSucc b} _ _ | record { quot = succ quot ; rem = succ rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = inl quotSmall } = record { quotient = negSucc quot ; rem = nonneg (succ rem) ; remSmall = inr ((λ ()) , remIsSmall) ; divAlg = applyEquality nonneg (transitivity (equalityCommutative pr) (applyEquality (λ i → i +N succ rem) (multiplicationNIsCommutative (succ b) (succ quot)))) }
  divAlg {negSucc a} {nonneg zero} _ b!=0 = exFalso (b!=0 refl)
  divAlg {negSucc a} {nonneg (succ b)} _ _ with divisionAlg (succ b) (succ a)
  divAlg {negSucc a} {nonneg (succ b)} _ _ | record { quot = zero ; rem = zero ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = exFalso (naughtE (transitivity (equalityCommutative (transitivity (Semiring.sumZeroRight ℕSemiring _) (multiplicationNIsCommutative b 0))) pr))
  divAlg {negSucc a} {nonneg (succ b)} _ _ | record { quot = succ quot ; rem = zero ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = record { quotient = negSucc quot ; rem = nonneg 0 ; remSmall = inl refl ; divAlg = applyEquality negSucc (succInjective (transitivity (equalityCommutative pr) t)) }
    where
      t : succ (quot +N b *N succ quot) +N 0 ≡ succ ((quot +N b *N quot) +N b)
      t rewrite Semiring.sumZeroRight ℕSemiring (succ (quot +N b *N succ quot)) | Semiring.commutative ℕSemiring (quot +N b *N quot) b | Semiring.+Associative ℕSemiring b quot (b *N quot) | Semiring.commutative ℕSemiring b quot | equalityCommutative (Semiring.+Associative ℕSemiring quot b (b *N quot)) | multiplicationNIsCommutative b (succ quot) | multiplicationNIsCommutative quot b = refl
  divAlg {negSucc a} {nonneg (succ b)} _ _ | record { quot = zero ; rem = succ rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } rewrite multiplicationNIsCommutative b 0 | equalityCommutative (succInjective pr) = record { quotient = nonneg zero ; rem = negSucc rem ; remSmall = inr (((λ ()) , remIsSmall)) ; divAlg = refl }
  divAlg {negSucc a} {nonneg (succ b)} _ _ | record { quot = succ quot ; rem = succ rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = record { quotient = negSucc quot ; rem = negSucc rem ; remSmall = inr ((λ ()) , remIsSmall) ; divAlg = applyEquality negSucc (succInjective (transitivity (equalityCommutative pr) t)) }
    where
      t : succ b *N succ quot +N succ rem ≡ succ (succ (succ b *N quot +N b) +N rem)
      t rewrite Semiring.commutative ℕSemiring ((quot +N b *N quot) +N b) rem | Semiring.commutative ℕSemiring (succ rem) ((quot +N b *N quot) +N b) | multiplicationNIsCommutative b (succ quot) | equalityCommutative (Semiring.+Associative ℕSemiring quot (b *N quot) b) | Semiring.commutative ℕSemiring b (quot *N b) | multiplicationNIsCommutative b quot = refl
  divAlg {negSucc a} {negSucc b} _ _ with divisionAlg (succ b) (succ a)
  divAlg {negSucc a} {negSucc b} _ _ | record { quot = zero ; rem = zero ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = exFalso (naughtE (transitivity (equalityCommutative (transitivity (Semiring.sumZeroRight ℕSemiring (b *N 0)) (multiplicationNIsCommutative b 0))) pr))
  divAlg {negSucc a} {negSucc b} _ _ | record { quot = zero ; rem = succ rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } rewrite multiplicationNIsCommutative b 0 | equalityCommutative (succInjective pr) = record { quotient = nonneg 0 ; rem = negSucc rem ; remSmall = inr ((λ ()) , remIsSmall) ; divAlg = refl }
  divAlg {negSucc a} {negSucc b} _ _ | record { quot = succ quot ; rem = zero ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = record { quotient = nonneg (succ quot) ; rem = nonneg 0 ; remSmall = inl refl ; divAlg = applyEquality negSucc (succInjective (transitivity (equalityCommutative pr) t)) }
    where
      t : succ ((quot +N b *N succ quot) +N 0) ≡ succ ((b +N quot *N b) +N quot)
      t = {!!}
  divAlg {negSucc a} {negSucc b} _ _ | record { quot = succ quot ; rem = succ rem ; pr = pr ; remIsSmall = inl remIsSmall ; quotSmall = quotSmall } = {!!}

ℤEuclideanDomain : EuclideanDomain ℤRing
EuclideanDomain.isIntegralDomain ℤEuclideanDomain = ℤIntDom
EuclideanDomain.norm ℤEuclideanDomain = norm'
EuclideanDomain.normSize ℤEuclideanDomain = normSize
EuclideanDomain.divisionAlg ℤEuclideanDomain {a} {b} a!=0 b!=0 = divAlg {a} {b} a!=0 b!=0
