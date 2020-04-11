{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Numbers.Naturals.Order.WellFounded
open import Numbers.Primes.PrimeNumbers
open import Semirings.Definition
open import Orders.Total.Definition
open import Orders.WellFounded.Induction
open import Numbers.Naturals.EuclideanAlgorithm

module Numbers.Primes.IntegerFactorisation where
open TotalOrder ℕTotalOrder

-- Represent a factorisation into increasing factors
-- Note that 0 cannot be expressed this way.
record factorisationNonunit (minFactor : ℕ) (a : ℕ) : Set where
  inductive
  field
    1<a : 1 <N a
    firstFactor : ℕ
    firstFactorNontrivial : 1 <N firstFactor
    firstFactorBiggerMin : minFactor ≤N firstFactor
    firstFactorDivision : divisionAlgResult firstFactor a
    firstFactorDivides : divisionAlgResult.rem firstFactorDivision ≡ 0
    firstFactorPrime : Prime firstFactor
    otherFactorsNumber : ℕ
    otherFactors : ((divisionAlgResult.quot firstFactorDivision ≡ 1) && (otherFactorsNumber ≡ 0)) || (((1 <N divisionAlgResult.quot firstFactorDivision) && (factorisationNonunit firstFactor (divisionAlgResult.quot firstFactorDivision))))

private
  lemma : (p : ℕ) → p *N 1 +N 0 ≡ p
  lemma p rewrite Semiring.sumZeroRight ℕSemiring (p *N 1) | Semiring.productOneRight ℕSemiring p = refl

  lemma' : {a b : ℕ} → a *N zero +N 0 ≡ b → b ≡ zero
  lemma' {a} {b} pr rewrite Semiring.sumZeroRight ℕSemiring (a *N zero) | Semiring.productZeroRight ℕSemiring a = equalityCommutative pr

primeFactorisation : {p : ℕ} → (pr : Prime p) → factorisationNonunit 1 p
primeFactorisation {p} record { p>1 = p>1 ; pr = pr } = record {1<a = p>1 ; firstFactor = p ; firstFactorNontrivial = p>1 ; firstFactorBiggerMin = inl p>1 ; firstFactorDivision = record { quot = 1 ; rem = 0 ; pr = lemma p  ; remIsSmall = zeroIsValidRem p ; quotSmall = inl (TotalOrder.<Transitive ℕTotalOrder (le zero refl) p>1) } ; firstFactorDivides = refl ; firstFactorPrime = record { p>1 = p>1 ; pr = pr} ; otherFactors = inl record { fst = refl ; snd = refl } ; otherFactorsNumber = 0 }
  where
    proof : (s : ℕ) → s *N 1 +N 0 ≡ s
    proof s rewrite Semiring.sumZeroRight ℕSemiring (s *N 1) | multiplicationNIsCommutative s 1 | Semiring.sumZeroRight ℕSemiring s = refl

twoAsFact : factorisationNonunit 2 2
factorisationNonunit.1<a twoAsFact = succPreservesInequality (succIsPositive 0)
factorisationNonunit.firstFactor twoAsFact = 2
factorisationNonunit.firstFactorNontrivial twoAsFact = succPreservesInequality (succIsPositive 0)
factorisationNonunit.firstFactorBiggerMin twoAsFact = inr refl
factorisationNonunit.firstFactorDivision twoAsFact = record { quot = 1 ; rem = 0 ; remIsSmall = zeroIsValidRem 2 ; pr = refl ; quotSmall = inl (le 1 refl) }
factorisationNonunit.firstFactorDivides twoAsFact = refl
factorisationNonunit.firstFactorPrime twoAsFact = twoIsPrime
factorisationNonunit.otherFactorsNumber twoAsFact = 0
factorisationNonunit.otherFactors twoAsFact = inl record { fst = refl ; snd = refl }

fourFact : factorisationNonunit 1 4
factorisationNonunit.1<a fourFact = succPreservesInequality (succIsPositive 2)
factorisationNonunit.firstFactor fourFact = 2
factorisationNonunit.firstFactorNontrivial fourFact = succPreservesInequality (succIsPositive 0)
factorisationNonunit.firstFactorBiggerMin fourFact = inl (succPreservesInequality (succIsPositive 0))
factorisationNonunit.firstFactorDivision fourFact = record { quot = 2 ; rem = 0 ; remIsSmall = zeroIsValidRem 2 ; pr = refl ; quotSmall = inl (le 1 refl) }
factorisationNonunit.firstFactorDivides fourFact = refl
factorisationNonunit.firstFactorPrime fourFact = twoIsPrime
factorisationNonunit.otherFactorsNumber fourFact = 1
factorisationNonunit.otherFactors fourFact = inr record { fst = succPreservesInequality (succIsPositive 0) ; snd = twoAsFact }

lessLemma : {y : ℕ} → (1 <N y) → (zero <N y)
lessLemma {.(succ (x +N 1))} (le x refl) = succIsPositive (x +N 1)

canReduceFactorBound : {a i j : ℕ} → factorisationNonunit i a → j <N i → factorisationNonunit j a
canReduceFactorBound {a} {i} {j} record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = inl ff<i ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = otherFactors } j<i = record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = inl (lessTransitive j<i ff<i) ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = otherFactors }
canReduceFactorBound {a} {i} {j} record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = inr ff=i ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = otherFactors } j<i = record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = inl (identityOfIndiscernablesRight _<N_ j<i ff=i) ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = otherFactors }

canReduceFactorBound' : {a i j : ℕ} → factorisationNonunit i a → j ≤N i → factorisationNonunit j a
canReduceFactorBound' {a} {i} {j} factA (inl x) = canReduceFactorBound factA x
canReduceFactorBound' {a} {i} {.i} factA (inr refl) = factA

canIncreaseFactorBound : {a i : ℕ} → (fact : factorisationNonunit 1 a) → (∀ x → 1 <N x → x <N i → x ∣ a → False) → (i ≤N factorisationNonunit.firstFactor fact) → factorisationNonunit i a
canIncreaseFactorBound {a} {i} record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = firstFactorBiggerMin ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = otherFactors } noSmaller iSmallEnough = record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = Prime.p>1 firstFactorPrime ; firstFactorBiggerMin = iSmallEnough ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = otherFactors }

-- Get the smallest prime factor of the number
everyNumberHasAPrimeFactor : {a : ℕ} → (1 <N a) → Sg ℕ (λ i → ((i ∣ a) && (1 <N i)) && ((Prime i) && (∀ x → x <N i → 1 <N x → x ∣ a → False)))
everyNumberHasAPrimeFactor {a} 1<a with compositeOrPrime a 1<a
everyNumberHasAPrimeFactor {a} 1<a | inl record { n>1 = n>1 ; divisor = divisor ; dividesN = dividesN ; divisorLessN = divisorLessN ; divisorNot1 = divisorNot1 ; divisorPrime = divisorPrime ; noSmallerDivisors = noSmallerDivisors } = ( divisor , record { fst = record { fst = dividesN ; snd = divisorNot1 } ; snd = record { fst = divisorPrime ; snd = noSmallerDivisors } } )
everyNumberHasAPrimeFactor {a} 1<a | inr x = (a , record { fst = record { fst = aDivA a ; snd = 1<a } ; snd = record { fst = x ; snd = λ y y<a 1<y y|a → irreflexive (<WellDefined (equalityCommutative (Prime.pr x y|a y<a (lessLemma 1<y))) refl 1<y) }} )

lemma2 : {a b c : ℕ} → 1 <N a → 0 <N b → a *N b +N 0 ≡ c → b <N c
lemma2 {zero} {b} {c} 1<a _ pr = exFalso (zeroNeverGreater 1<a)
lemma2 {succ zero} {b} {c} 1<a _ pr = exFalso (lessIrreflexive 1<a)
lemma2 {succ (succ a)} {zero} {zero} 1<a t pr = exFalso (lessIrreflexive t)
lemma2 {succ (succ a)} {zero} {succ c} 1<a t pr = succIsPositive c
lemma2 {succ (succ a)} {succ b} {c} 1<a t pr = le (b +N (a *N succ b)) go
  where
    assocLemm : (a b c : ℕ) → (a +N b) +N c ≡ (a +N c) +N b
    assocLemm a b c rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) | Semiring.commutative ℕSemiring b c | Semiring.+Associative ℕSemiring a c b = refl
    go : succ ((b +N a *N succ b) +N succ b) ≡ c
    go rewrite Semiring.sumZeroRight ℕSemiring (succ (b +N succ (b +N a *N succ b))) | equalityCommutative (assocLemm b (succ b) (a *N succ b)) | Semiring.+Associative ℕSemiring b (succ b) (a *N succ b) = pr

factorIntegerLemma : (x : ℕ) (indHyp : (y : ℕ) (y<x : y <N x) → ((y <N 2) || (factorisationNonunit 1 y))) → ((x <N 2) || (factorisationNonunit 1 x))
factorIntegerLemma zero indHyp = inl (succIsPositive 1)
factorIntegerLemma (succ zero) indHyp = inl (succPreservesInequality (succIsPositive 0))
factorIntegerLemma (succ (succ x)) indHyp with everyNumberHasAPrimeFactor {succ (succ x)} (succPreservesInequality (succIsPositive x))
factorIntegerLemma (succ (succ x)) indHyp | a , record { fst = record { fst = divides record {quot = zero ; rem = .0 ; pr = ssxDivA ; remIsSmall = r } refl ; snd = 1<a }; snd = record { fst = primeA ; snd = smallerFactors } } rewrite Semiring.sumZeroRight ℕSemiring (a *N zero) | multiplicationNIsCommutative a 0 = exFalso (naughtE ssxDivA)
factorIntegerLemma (succ (succ x)) indHyp | a , record { fst = record { fst = divides record {quot = succ zero ; rem = .0 ; pr = ssxDivA ; remIsSmall = r } refl ; snd = 1<a }; snd = record { fst = primeA ; snd = smallerFactors } } = inr record { 1<a = succPreservesInequality (succIsPositive x) ; firstFactor = a ; firstFactorNontrivial = Prime.p>1 primeA ; firstFactorBiggerMin = inl (Prime.p>1 primeA) ; firstFactorDivision = record { quot = 1 ; rem = 0 ; pr = ssxDivA ; remIsSmall = r ; quotSmall = inl (TotalOrder.<Transitive ℕTotalOrder (le zero refl) 1<a) } ; firstFactorDivides = refl ; firstFactorPrime = record { p>1 = Prime.p>1 primeA ; pr = Prime.pr primeA } ; otherFactors = inl record { fst = refl ; snd = refl } ; otherFactorsNumber = 0 }

factorIntegerLemma (succ (succ x)) indHyp | a , record { fst = record { fst = divides record {quot = succ (succ qu) ; rem = .0 ; pr = ssxDivA ; remIsSmall = remSmall } refl ; snd = 1<a }; snd = record { fst = primeA ; snd = smallerFactors } } = inr record { 1<a = succPreservesInequality (succIsPositive x) ; firstFactor = a ; firstFactorNontrivial = Prime.p>1 primeA ; firstFactorBiggerMin = inl (Prime.p>1 primeA) ; firstFactorDivision = record { quot = succ (succ qu) ; rem = 0 ; pr = ssxDivA ; remIsSmall = remSmall ; quotSmall = inl (TotalOrder.<Transitive ℕTotalOrder (le zero refl) 1<a) } ; firstFactorDivides = refl ; firstFactorPrime = record { p>1 = Prime.p>1 primeA ; pr = Prime.pr primeA } ; otherFactors = inr record {fst = succPreservesInequality (succIsPositive qu) ; snd = factNonunit} ; otherFactorsNumber = succ (factorisationNonunit.otherFactorsNumber indHypRes') }
  where
    indHypRes : ((succ (succ qu)) <N 2) || factorisationNonunit 1 (succ (succ qu))
    indHypRes = indHyp (succ (succ qu)) (lemma2 {a} {succ (succ qu)} {succ (succ x)} 1<a (succIsPositive (succ qu)) ssxDivA)
    indHypRes' : factorisationNonunit 1 (succ (succ qu))
    indHypRes' with indHypRes
    indHypRes' | inl y = exFalso (zeroNeverGreater (canRemoveSuccFrom<N (canRemoveSuccFrom<N y)))
    indHypRes' | inr y = y
    z|ssx : (z : ℕ) → z ∣ succ (succ qu) → z ∣ succ (succ x)
    z|ssx z z|ssq = (divisibilityTransitive z|ssq (divides (record { quot = a ; rem = 0 ; pr = identityOfIndiscernablesLeft _≡_ ssxDivA (applyEquality (λ t → t +N 0) (multiplicationNIsCommutative a (succ (succ qu)))) ; remIsSmall = zeroIsValidRem (succ (succ qu)) ; quotSmall = inl (succIsPositive _) }) refl))
    factNonunit : factorisationNonunit a (succ (succ qu))
    factNonunit with totality a (factorisationNonunit.firstFactor indHypRes')
    factNonunit | inl (inl a<ff) = canIncreaseFactorBound indHypRes' (λ z 1<z z<a z|ssq → smallerFactors z z<a 1<z (z|ssx z z|ssq)) (inl a<ff)
    factNonunit | inl (inr ff<a) = exFalso (smallerFactors (factorisationNonunit.firstFactor indHypRes') ff<a (factorisationNonunit.firstFactorNontrivial indHypRes') (z|ssx (factorisationNonunit.firstFactor indHypRes') (divides (factorisationNonunit.firstFactorDivision indHypRes') (factorisationNonunit.firstFactorDivides indHypRes'))))
    factNonunit | inr ff=a = canIncreaseFactorBound indHypRes' (λ z 1<z z<a z|ssq → smallerFactors z z<a 1<z (divisibilityTransitive z|ssq (divides (record { quot = a ; rem = 0 ; pr = identityOfIndiscernablesLeft _≡_ ssxDivA (applyEquality (λ t → t +N 0) (multiplicationNIsCommutative a (succ (succ qu)))) ; remIsSmall = zeroIsValidRem (succ (succ qu)) ; quotSmall = inl (succIsPositive _) }) refl))) (inr ff=a)

factorInteger : (a : ℕ) → (1 <N a) → factorisationNonunit 1 a
factorInteger a 1<a with (rec <NWellfounded (λ n → (n <N 2) || (factorisationNonunit 1 n))) factorIntegerLemma
... | bl with bl a
factorInteger a 1<a | bl | inl x = exFalso (noIntegersBetweenXAndSuccX 1 1<a x)
factorInteger a 1<a | bl | inr x = x

lessTransLemma : {p i j : ℕ} → p <N i → i ≤N j → p <N j
lessTransLemma {p} {i} {j} p<i (inl x) = <Transitive p<i x
lessTransLemma {p} {i} {j} p<i (inr x) rewrite x = p<i

lemma4' : {quot rem b : ℕ} → (quot +N quot) +N rem ≡ succ b → quot <N succ b
lemma4' {zero} {rem} {b} pr = succIsPositive b
lemma4' {succ quot} {rem} {b} pr rewrite equalityCommutative (Semiring.+Associative ℕSemiring quot (succ quot) rem) = succPreservesInequality (le (quot +N rem) (succInjective (transitivity (applyEquality succ (Semiring.commutative ℕSemiring _ quot)) pr)))

lemma4 : {quot a rem b : ℕ} → (a *N quot +N rem ≡ succ b) → (1 <N a) → (quot <N succ b)
lemma4 {quot} {zero} {rem} {b} pr 1<a = exFalso (zeroNeverGreater 1<a)
lemma4 {quot} {succ zero} {rem} {b} pr 1<a = exFalso (lessIrreflexive 1<a)
lemma4 {quot} {succ (succ zero)} {rem} {b} pr 1<a rewrite Semiring.sumZeroRight ℕSemiring quot = lemma4' pr
lemma4 {quot} {succ (succ (succ a))} {rem} {b} pr 1<a = lemma4 {quot} {succ (succ a)} {quot +N rem} {b} p' (succPreservesInequality (succIsPositive a))
  where
    p' : (quot +N (quot +N a *N quot)) +N (quot +N rem) ≡ succ b
    p' rewrite Semiring.commutative ℕSemiring quot (quot +N (quot +N a *N quot)) | Semiring.+Associative ℕSemiring (quot +N (quot +N a *N quot)) quot rem = pr

noSmallerFactors : {a i p : ℕ} → (factorisationNonunit i a) → (Prime p) → (p <N i) → (p ∣ a) → False
noSmallerFactors {a} {i} {p} factA pPrime p<i p|a with rec <NWellfounded (λ b → (factorisationNonunit i b) → p ∣ b → False)
... | indHyp = (indHyp prf) a factA p|a
  where
    prf : (x : ℕ) (ind : (y : ℕ) (y<x : y <N x) (factY : factorisationNonunit i y) (p|y : p ∣ y) → False) (factX : factorisationNonunit i x) (p|x : p ∣ x) → False
    prf x ind record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = firstFactorBiggerMin ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = (inl record { fst = quotFirstfact=1 ; snd = otherFactorsNumber }) } p|x = exFalso bad
      where
        x=firstFact : firstFactor *N 1 +N 0 ≡ x
        x=firstFact rewrite equalityCommutative firstFactorDivides | equalityCommutative quotFirstfact=1 = divisionAlgResult.pr firstFactorDivision
        x=firstFact' : firstFactor ≡ x
        x=firstFact' = transitivity (equalityCommutative (lemma firstFactor)) x=firstFact
        p|firstFact : p ∣ firstFactor
        p|firstFact rewrite x=firstFact' = p|x
        p=firstFact : p ≡ firstFactor
        p=firstFact = primeDivPrimeImpliesEqual pPrime firstFactorPrime p|firstFact
        i<=firstFactor : i ≤N p
        i<=firstFactor rewrite p=firstFact = firstFactorBiggerMin
        bad : False
        bad with i<=firstFactor
        ... | inl t = TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder t p<i)
        ... | inr eq rewrite eq = TotalOrder.irreflexive ℕTotalOrder p<i
    prf zero ind record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = firstFactorBiggerMin ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = (inr otherFact) } p|x = zeroNeverGreater 1<a
    prf (succ x) ind record { 1<a = 1<a ; firstFactor = firstFactor ; firstFactorNontrivial = firstFactorNontrivial ; firstFactorBiggerMin = firstFactorBiggerMin ; firstFactorDivision = firstFactorDivision ; firstFactorDivides = firstFactorDivides ; firstFactorPrime = firstFactorPrime ; otherFactors = (inr otherFact) } p|x = ind (divisionAlgResult.quot firstFactorDivision) (lemma4 {divisionAlgResult.quot firstFactorDivision} {firstFactor} {divisionAlgResult.rem firstFactorDivision} {x} (divisionAlgResult.pr (firstFactorDivision)) (primesAreBiggerThanOne firstFactorPrime)) (canReduceFactorBound' (_&&_.snd otherFact) firstFactorBiggerMin) (p|q p|ffOrQ)
      where
        succXNotSmaller : succ x <N firstFactor → False
        succXNotSmaller = divisorIsSmaller {firstFactor} {x} (divides firstFactorDivision firstFactorDivides)
        succXNotSmaller' : firstFactor ≤N succ x
        succXNotSmaller' = notSmallerMeansGE succXNotSmaller
        inter : firstFactor *N (divisionAlgResult.quot firstFactorDivision) +N divisionAlgResult.rem firstFactorDivision ≡ (succ x)
        inter = divisionAlgResult.pr firstFactorDivision
        inter' : firstFactor *N (divisionAlgResult.quot firstFactorDivision) +N 0 ≡ (succ x)
        inter' rewrite equalityCommutative firstFactorDivides = inter
        inter'' : firstFactor *N (divisionAlgResult.quot firstFactorDivision) ≡ (succ x)
        inter'' rewrite equalityCommutative (Semiring.sumZeroRight ℕSemiring (firstFactor *N (divisionAlgResult.quot firstFactorDivision))) = inter'
        p|ff*q : p ∣ firstFactor *N (divisionAlgResult.quot firstFactorDivision)
        p|ff*q rewrite inter'' = p|x
        p|ffOrQ : (p ∣ firstFactor) || (p ∣ divisionAlgResult.quot firstFactorDivision)
        p|ffOrQ = primesArePrime pPrime p|ff*q
        p|ffIsFalse : (p ∣ firstFactor) → False
        p|ffIsFalse p|ff = lessIrreflexive (lessTransLemma p<i i<=p)
          where
            p=ff : p ≡ firstFactor
            p=ff = primeDivPrimeImpliesEqual pPrime firstFactorPrime p|ff
            i<=p : i ≤N p
            i<=p rewrite p=ff = firstFactorBiggerMin
        p|q : ((p ∣ firstFactor) || (p ∣ divisionAlgResult.quot firstFactorDivision)) → (p ∣ divisionAlgResult.quot firstFactorDivision)
        p|q (inl fls) = exFalso (p|ffIsFalse fls)
        p|q (inr res) = res

lemma3 : {a : ℕ} → a ≡ 0 → 1 <N a → False
lemma3 {a} a=0 pr rewrite a=0 = zeroNeverGreater pr

firstFactorUniqueLemma : {i : ℕ} → (a : ℕ) → (1 <N a) → (f1 : factorisationNonunit i a) → (f2 : factorisationNonunit i a) → (factorisationNonunit.firstFactor f1 <N factorisationNonunit.firstFactor f2) → False
firstFactorUniqueLemma {i} a 1<a f1 f2 ff1<ff2 = go
  where
    p1 = factorisationNonunit.firstFactor f1
    rem1 = divisionAlgResult.quot (factorisationNonunit.firstFactorDivision f1)
    p2 = factorisationNonunit.firstFactor f2
    rem2 = divisionAlgResult.quot (factorisationNonunit.firstFactorDivision f2)
    p1<p2 : p1 <N p2
    p1<p2 = ff1<ff2
    a=p2rem2 : a ≡ p2 *N rem2
    a=p2rem2 with divisionAlgResult.pr (factorisationNonunit.firstFactorDivision f2)
    ... | ff rewrite factorisationNonunit.firstFactorDivides f2 | Semiring.sumZeroRight ℕSemiring (factorisationNonunit.firstFactor f2 *N divisionAlgResult.quot (factorisationNonunit.firstFactorDivision f2)) = equalityCommutative ff
    p1|second : (p1 ∣ p2) || (p1 ∣ rem2)
    p1|second = primesArePrime {p1} {p2} {rem2} (factorisationNonunit.firstFactorPrime f1) lem
      where
        lem : p1 ∣ (p2 *N rem2)
        lem = identityOfIndiscernablesRight _∣_ (divides (factorisationNonunit.firstFactorDivision f1) (factorisationNonunit.firstFactorDivides f1)) a=p2rem2
    p1|second' : ((p1 ∣ p2) || (p1 ∣ rem2)) → ((p1 ≡ p2) || (p1 ∣ rem2))
    p1|second' (inl x) = inl (primeDivPrimeImpliesEqual (factorisationNonunit.firstFactorPrime f1) (factorisationNonunit.firstFactorPrime f2) x)
    p1|second' (inr x) = inr x
    p1|second'' : (p1 ≡ p2) || (p1 ∣ rem2)
    p1|second'' = p1|second' p1|second
    go : False
    go with p1|second''
    go | inl x = irreflexive (<WellDefined x refl ff1<ff2)
    go | inr x with factorisationNonunit.otherFactors f2
    go | inr x | inl record { fst = rem2=1 ; snd = _ } rewrite rem2=1 = exFalso (oneIsNotPrime res)
      where
        1prime' : Prime p1 ≡ Prime 1
        1prime' = applyEquality Prime (oneHasNoDivisors x)
        res : Prime 1
        res rewrite equalityCommutative 1prime' = (factorisationNonunit.firstFactorPrime f1)
    go | inr x | inr p1|rem2 with factorisationNonunit.otherFactors f2
    go | inr x | inr p1|rem2 | inl record { fst = rem2=1 ; snd = _ } rewrite rem2=1 = exFalso (oneIsNotPrime res)
      where
        1prime' : Prime p1 ≡ Prime 1
        1prime' = applyEquality Prime (oneHasNoDivisors x)
        res : Prime 1
        res rewrite equalityCommutative 1prime' = (factorisationNonunit.firstFactorPrime f1)
    go | inr x | inr p1|rem2 | inr factorRem2 = noSmallerFactors (_&&_.snd factorRem2) (factorisationNonunit.firstFactorPrime f1) p1<p2 x

firstFactorUnique : {i : ℕ} → (a : ℕ) → (1 <N a) → (f1 : factorisationNonunit i a) → (f2 : factorisationNonunit i a) → (factorisationNonunit.firstFactor f1 ≡ factorisationNonunit.firstFactor f2)
firstFactorUnique {i} a 1<a f1 f2 with totality (factorisationNonunit.firstFactor f1) (factorisationNonunit.firstFactor f2)
firstFactorUnique {i} a 1<a f1 f2 | inl (inl f1<f2) = exFalso (firstFactorUniqueLemma a 1<a f1 f2 f1<f2)
firstFactorUnique {i} a 1<a f1 f2 | inl (inr f2<f1) = exFalso (firstFactorUniqueLemma a 1<a f2 f1 f2<f1)
firstFactorUnique {i} a 1<a f1 f2 | inr x = x

factorListLemma : {i : ℕ} → (a : ℕ) → (1 <N a) → (f1 : factorisationNonunit i a) → (f2 : factorisationNonunit i a) → (divisionAlgResult.quot (factorisationNonunit.firstFactorDivision f2)) ≡ (divisionAlgResult.quot (factorisationNonunit.firstFactorDivision f1))
factorListLemma {i} a 1<a f1 f2 with firstFactorUnique {i} a 1<a f1 f2
... | firstFactEqual = res
  where
    div1 : divisionAlgResult (factorisationNonunit.firstFactor f1) a
    div1 = factorisationNonunit.firstFactorDivision f1
    rem1=0 : divisionAlgResult.rem div1 ≡ 0
    rem1=0 = factorisationNonunit.firstFactorDivides f1
    pr1 : (factorisationNonunit.firstFactor f1) *N (divisionAlgResult.quot div1) +N 0 ≡ a
    pr1 rewrite equalityCommutative rem1=0 = divisionAlgResult.pr div1
    pr1' : (factorisationNonunit.firstFactor f1) *N (divisionAlgResult.quot div1) ≡ a
    pr1' rewrite equalityCommutative (Semiring.sumZeroRight ℕSemiring ((factorisationNonunit.firstFactor f1) *N (divisionAlgResult.quot div1))) = pr1
    div2 : divisionAlgResult (factorisationNonunit.firstFactor f2) a
    div2 = factorisationNonunit.firstFactorDivision f2
    rem2=0 : divisionAlgResult.rem div2 ≡ 0
    rem2=0 = factorisationNonunit.firstFactorDivides f2
    pr2 : (factorisationNonunit.firstFactor f2) *N (divisionAlgResult.quot div2) +N 0 ≡ a
    pr2 rewrite equalityCommutative rem2=0 = divisionAlgResult.pr div2
    pr2' : (factorisationNonunit.firstFactor f2) *N (divisionAlgResult.quot div2) ≡ a
    pr2' rewrite equalityCommutative (Semiring.sumZeroRight ℕSemiring ((factorisationNonunit.firstFactor f2) *N (divisionAlgResult.quot div2))) = pr2
    pr : (factorisationNonunit.firstFactor f2) *N (divisionAlgResult.quot div2) ≡ (factorisationNonunit.firstFactor f1) *N (divisionAlgResult.quot div1)
    pr = transitivity pr2' (equalityCommutative pr1')
    pr' : (factorisationNonunit.firstFactor f1) *N (divisionAlgResult.quot div2) ≡ (factorisationNonunit.firstFactor f1) *N (divisionAlgResult.quot div1)
    pr' = identityOfIndiscernablesLeft _≡_ pr (applyEquality (λ t → t *N divisionAlgResult.quot div2) (equalityCommutative firstFactEqual))
    positive : zero <N factorisationNonunit.firstFactor f1
    positive = lessTransitive (succIsPositive 0) (factorisationNonunit.firstFactorNontrivial f1)
    res : divisionAlgResult.quot div2 ≡ divisionAlgResult.quot div1
    res = productCancelsLeft (factorisationNonunit.firstFactor f1) (divisionAlgResult.quot div2) (divisionAlgResult.quot div1) positive pr'

factorListSameLength : {i : ℕ} → (a : ℕ) → (1 <N a) → (f1 : factorisationNonunit i a) → (f2 : factorisationNonunit i a) → (divisionAlgResult.quot (factorisationNonunit.firstFactorDivision f1) ≡ 1) → divisionAlgResult.quot (factorisationNonunit.firstFactorDivision f2) ≡ 1
factorListSameLength {i} a 1<a f1 f2 quot=1 with firstFactorUnique {i} a 1<a f1 f2
... | firstFactEqual with factorListLemma {i} a 1<a f1 f2
... | eq = transitivity eq quot=1
