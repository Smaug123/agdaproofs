{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.WellFounded
open import Numbers.Naturals.Order.Lemmas
open import Numbers.Integers.Definition
open import Numbers.Integers.Integers
open import Numbers.Integers.Order
open import Groups.Groups
open import Groups.Definition
open import Rings.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Fields.Fields
open import Numbers.Primes.PrimeNumbers
open import Setoids.Setoids
open import Setoids.Orders
open import Functions
open import Sets.EquivalenceRelations
open import Numbers.Rationals.Definition
open import Semirings.Definition
open import Orders.Total.Definition
open import Orders.WellFounded.Induction

module Numbers.Rationals.Lemmas where

open import Semirings.Lemmas ℕSemiring

open PartiallyOrderedRing ℤPOrderedRing
open import Rings.Orders.Total.Lemmas ℤOrderedRing
open SetoidTotalOrder (totalOrderToSetoidTotalOrder ℤOrder)

evenOrOdd : (a : ℕ) → (Sg ℕ (λ i → i *N 2 ≡ a)) || (Sg ℕ (λ i → succ (i *N 2) ≡ a))
evenOrOdd zero = inl (zero , refl)
evenOrOdd (succ zero) = inr (zero , refl)
evenOrOdd (succ (succ a)) with evenOrOdd a
evenOrOdd (succ (succ a)) | inl (a/2 , even) = inl (succ a/2 , applyEquality (λ i → succ (succ i)) even)
evenOrOdd (succ (succ a)) | inr (a/2-1 , odd) = inr (succ a/2-1 , applyEquality (λ i → succ (succ i)) odd)

parity : (a b : ℕ) → succ (2 *N a) ≡ 2 *N b → False
parity zero (succ b) pr rewrite Semiring.commutative ℕSemiring b (succ (b +N 0)) = bad pr
  where
    bad : (1 ≡ succ (succ ((b +N 0) +N b))) → False
    bad ()
parity (succ a) (succ b) pr rewrite Semiring.commutative ℕSemiring b (succ (b +N 0)) | Semiring.commutative ℕSemiring a (succ (a +N 0)) | Semiring.commutative ℕSemiring (a +N 0) a | Semiring.commutative ℕSemiring (b +N 0) b = parity a b (succInjective (succInjective pr))

sqrt0 : (p : ℕ) → p *N p ≡ 0 → p ≡ 0
sqrt0 zero pr = refl
sqrt0 (succ p) ()

-- So as to give us something easy to induct down, introduce a silly extra variable
evil' : (k : ℕ) → ((a b : ℕ) → (0 <N a) → (pr : k ≡ a +N b) → a *N a ≡ (b *N b) *N 2 → False)
evil' = rec <NWellfounded (λ z → (x x₁ : ℕ) (pr' : 0 <N x) (x₂ : z ≡ x +N x₁) (x₃ : x *N x ≡ (x₁ *N x₁) *N 2) → False) go
  where
    go : (k : ℕ) (indHyp : (k' : ℕ) (k'<k : k' <N k) (r s : ℕ) (0<r : 0 <N r) (r+s : k' ≡ r +N s) (x₇ : r *N r ≡ (s *N s) *N 2) → False) (a b : ℕ) (0<a : 0 <N a) (a+b : k ≡ a +N b) (pr : a *N a ≡ (b *N b) *N 2) → False
    go k indHyp a b 0<a a+b pr = contr
      where
        open import Semirings.Solver ℕSemiring multiplicationNIsCommutative
        aEven : Sg ℕ (λ i → i *N 2 ≡ a)
        aEven with evenOrOdd a
        aEven | inl x = x
        aEven | inr (a/2-1 , odd) rewrite equalityCommutative odd =
          -- Derive a pretty mechanical contradiction using the automatic solver.
          -- This line looks hellish, but it was almost completely mechanical.
          exFalso (parity (a/2-1 +N (a/2-1 *N succ (a/2-1 *N 2))) (b *N b) (transitivity (
            -- truly mechanical bit starts here
            from (succ (plus (plus (const a/2-1) (times (const a/2-1) (succ (times (const a/2-1) (succ (succ zero)))))) (plus (plus (const a/2-1) (times (const a/2-1) (succ (times (const a/2-1) (succ (succ zero)))))) (times zero (plus (const a/2-1) (times (const a/2-1) (succ (times (const a/2-1) (succ (succ zero))))))))))
            to succ (plus (times (const a/2-1) (succ (succ zero))) (times (times (const a/2-1) (succ (succ zero))) (succ (times (const a/2-1) (succ (succ zero))))))
            -- truly mechanical bit ends here
            by applyEquality (λ i → succ (a/2-1 +N i)) (
              -- Grinding out some manipulations
              transitivity (equalityCommutative (Semiring.+Associative ℕSemiring a/2-1 _ _)) (applyEquality (a/2-1 +N_) (transitivity (Semiring.commutative ℕSemiring (a/2-1 *N (a/2-1 +N a/2-1)) _) (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring a/2-1 _ _)) (applyEquality (a/2-1 +N_) (transitivity (equalityCommutative (Semiring.+Associative ℕSemiring a/2-1 _ _)) (applyEquality (a/2-1 +N_) (transitivity (equalityCommutative (Semiring.+DistributesOver* ℕSemiring a/2-1 _ _)) (applyEquality (a/2-1 *N_) (equalityCommutative (Semiring.+Associative ℕSemiring a/2-1 _ _))))))))))
            )) (transitivity pr (multiplicationNIsCommutative (b *N b) 2))))

        next : (underlying aEven *N 2) *N (underlying aEven *N 2) ≡ (b *N b) *N 2
        next with aEven
        ... | a/2 , even rewrite even = pr

        next2 : (underlying aEven *N 2) *N underlying aEven ≡ b *N b
        next2 = productCancelsRight 2 _ _ (le 1 refl) (transitivity (equalityCommutative (Semiring.*Associative ℕSemiring (underlying aEven *N 2) _ _)) next)

        next3 : b *N b ≡ (underlying aEven *N underlying aEven) *N 2
        next3 = equalityCommutative (transitivity (transitivity (equalityCommutative (Semiring.*Associative ℕSemiring (underlying aEven) _ _)) (multiplicationNIsCommutative (underlying aEven) _)) next2)

        halveDecreased : underlying aEven <N a
        halveDecreased with aEven
        halveDecreased | zero , even rewrite equalityCommutative even = exFalso (TotalOrder.irreflexive ℕTotalOrder 0<a)
        halveDecreased | succ a/2 , even = le a/2 (transitivity (applyEquality succ (transitivity (Semiring.commutative ℕSemiring a/2 _) (applyEquality succ (transitivity (doubleIsAddTwo a/2) (multiplicationNIsCommutative 2 a/2))))) even)

        reduced : b +N underlying aEven <N k
        reduced with lessRespectsAddition b halveDecreased
        ... | bl rewrite a+b = identityOfIndiscernablesLeft _<N_ bl (Semiring.commutative ℕSemiring _ b)

        0<b : 0 <N b
        0<b with TotalOrder.totality ℕTotalOrder 0 b
        0<b | inl (inl 0<b) = 0<b
        0<b | inl (inr ())
        0<b | inr 0=b rewrite equalityCommutative 0=b = exFalso (TotalOrder.irreflexive ℕTotalOrder {0} (identityOfIndiscernablesRight _<N_ 0<a (sqrt0 a pr)))

        contr : False
        contr = indHyp (b +N underlying aEven) reduced b (underlying aEven) 0<b refl next3

evil : (a b : ℕ) → (0 <N a) → a *N a ≡ (b *N b) *N 2 → False
evil a b 0<a = evil' (a +N b) a b 0<a refl

absNonneg : (x : ℕ) → abs (nonneg x) ≡ nonneg x
absNonneg x with totality (nonneg 0) (nonneg x)
absNonneg x | inl (inl 0<x) = refl
absNonneg x | inr 0=x = refl

absNegsucc : (x : ℕ) → abs (negSucc x) ≡ nonneg (succ x)
absNegsucc x with totality (nonneg 0) (negSucc x)
absNegsucc x | inl (inr _) = refl

toNats : (numerator denominator : ℤ) → (denominator ≡ nonneg 0 → False) → (abs numerator) *Z (abs numerator) ≡ ((abs denominator) *Z (abs denominator)) *Z nonneg 2 → Sg (ℕ && ℕ) (λ nats → ((_&&_.fst nats *N _&&_.fst nats) ≡ (_&&_.snd nats *N _&&_.snd nats) *N 2) && (_&&_.snd nats ≡ 0 → False))
toNats (nonneg num) (nonneg 0) pr _ = exFalso (pr refl)
toNats (nonneg num) (nonneg (succ denom)) _ pr = (num ,, (succ denom)) , (nonnegInjective (transitivity (transitivity (equalityCommutative (absNonneg (num *N num))) (absRespectsTimes (nonneg num) (nonneg num))) pr) ,, λ ())
toNats (nonneg num) (negSucc denom) _ pr = (num ,, succ denom) , (nonnegInjective (transitivity (transitivity (equalityCommutative (absNonneg (num *N num))) (absRespectsTimes (nonneg num) (nonneg num))) pr) ,, λ ())
toNats (negSucc num) (nonneg (succ denom)) _ pr = (succ num ,, succ denom) , (nonnegInjective pr ,, λ ())
toNats (negSucc num) (negSucc denom) _ pr = (succ num ,, succ denom) , (nonnegInjective pr ,, λ ())

sqrt2Irrational : (a : ℚ) → (a *Q a) =Q (injectionQ (nonneg 2)) → False
sqrt2Irrational (numerator ,, (denominator , denom!=0)) pr = bad
  where
    -- We have in hand `pr`, which is the following (almost by definition):
    pr' : (numerator *Z numerator) ≡ (denominator *Z denominator) *Z nonneg 2
    pr' = transitivity (equalityCommutative (transitivity (Ring.*Commutative ℤRing) (Ring.identIsIdent ℤRing))) pr

    -- Move into the naturals so that we can do nice divisibility things.
    lemma1 : abs ((denominator *Z denominator) *Z nonneg 2) ≡ (abs denominator *Z abs denominator) *Z nonneg 2
    lemma1 = transitivity (absRespectsTimes (denominator *Z denominator) (nonneg 2)) (applyEquality (_*Z nonneg 2) (absRespectsTimes denominator denominator))
    amenableToNaturals : (abs numerator) *Z (abs numerator) ≡ ((abs denominator) *Z (abs denominator)) *Z nonneg 2
    amenableToNaturals = transitivity (equalityCommutative (absRespectsTimes numerator numerator)) (transitivity (applyEquality abs pr') lemma1)

    naturalsStatement : Sg (ℕ && ℕ) (λ nats → ((_&&_.fst nats *N _&&_.fst nats) ≡ (_&&_.snd nats *N _&&_.snd nats) *N 2) && (_&&_.snd nats ≡ 0 → False))
    naturalsStatement = toNats numerator denominator denom!=0 amenableToNaturals

    bad : False
    bad with naturalsStatement
    bad | (num ,, 0) , (pr1 ,, pr2) = exFalso (pr2 refl)
    bad | (num ,, succ denom) , (pr1 ,, pr2) = evil num (succ denom) 0<num pr1
      where
        0<num : 0 <N num
        0<num with TotalOrder.totality ℕTotalOrder 0 num
        0<num | inl (inl 0<num) = 0<num
        0<num | inr 0=num rewrite equalityCommutative 0=num = exFalso (naughtE pr1)
