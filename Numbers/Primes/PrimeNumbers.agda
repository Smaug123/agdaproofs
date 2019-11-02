{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Addition -- TODO - remove this dependency
open import Numbers.Naturals.Multiplication -- TODO - remove this dependency
open import Numbers.Naturals.Order -- TODO - remove this dependency
open import Numbers.Naturals.WithK
open import WellFoundedInduction
open import KeyValue.KeyValue
open import Orders
open import Vectors
open import Maybe
open import WithK
open import Semirings.Definition

module Numbers.Primes.PrimeNumbers where

    record divisionAlgResult (a : ℕ) (b : ℕ) : Set where
      field
        quot : ℕ
        rem : ℕ
        pr : a *N quot +N rem ≡ b
        remIsSmall : (rem <N a) || (a ≡ 0)
        quotSmall : (0 <N a) || ((0 ≡ a) && (quot ≡ 0))

    divAlgLessLemma : (a b : ℕ) → (0 <N a) → (r : divisionAlgResult a b) → (divisionAlgResult.quot r ≡ 0) || (divisionAlgResult.rem r <N b)
    divAlgLessLemma zero b pr _ = exFalso (TotalOrder.irreflexive ℕTotalOrder pr)
    divAlgLessLemma (succ a) b _ record { quot = zero ; rem = a%b ; pr = pr ; remIsSmall = remIsSmall } = inl refl
    divAlgLessLemma (succ a) b _ record { quot = (succ a/b) ; rem = a%b ; pr = pr ; remIsSmall = remIsSmall } = inr record { x = a/b +N a *N succ (a/b) ; proof = pr }

    modUniqueLemma : {rem1 rem2 a : ℕ} → (quot1 quot2 : ℕ) → rem1 <N a → rem2 <N a → a *N quot1 +N rem1 ≡ a *N quot2 +N rem2 → rem1 ≡ rem2
    modUniqueLemma {rem1} {rem2} {a} zero zero rem1<a rem2<a pr rewrite Semiring.productZeroRight ℕSemiring a = pr
    modUniqueLemma {rem1} {rem2} {a} zero (succ quot2) rem1<a rem2<a pr rewrite Semiring.productZeroRight ℕSemiring a | pr | multiplicationNIsCommutative a (succ quot2) | equalityCommutative (Semiring.+Associative ℕSemiring a (quot2 *N a) rem2) = exFalso (cannotAddAndEnlarge' {a} {quot2 *N a +N rem2} rem1<a)
    modUniqueLemma {rem1} {rem2} {a} (succ quot1) zero rem1<a rem2<a pr rewrite Semiring.productZeroRight ℕSemiring a | equalityCommutative pr | multiplicationNIsCommutative a (succ quot1) | equalityCommutative (Semiring.+Associative ℕSemiring a (quot1 *N a) rem1) = exFalso (cannotAddAndEnlarge' {a} {quot1 *N a +N rem1} rem2<a)
    modUniqueLemma {rem1} {rem2} {a} (succ quot1) (succ quot2) rem1<a rem2<a pr rewrite multiplicationNIsCommutative a (succ quot1) | multiplicationNIsCommutative a (succ quot2) | equalityCommutative (Semiring.+Associative ℕSemiring a (quot1 *N a) rem1) | equalityCommutative (Semiring.+Associative ℕSemiring a (quot2 *N a) rem2) = modUniqueLemma {rem1} {rem2} {a} quot1 quot2 rem1<a rem2<a (go {a}{quot1}{rem1}{quot2}{rem2} pr)
      where
        go : {a quot1 rem1 quot2 rem2 : ℕ} → (a +N (quot1 *N a +N rem1) ≡ a +N (quot2 *N a +N rem2)) → a *N quot1 +N rem1 ≡ a *N quot2 +N rem2
        go {a} {quot1} {rem1} {quot2} {rem2} pr rewrite multiplicationNIsCommutative quot1 a | multiplicationNIsCommutative quot2 a = canSubtractFromEqualityLeft {a} pr

    modIsUnique : {a b : ℕ} → (div1 div2 : divisionAlgResult a b) → divisionAlgResult.rem div1 ≡ divisionAlgResult.rem div2
    modIsUnique {zero} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = remIsSmall1 } record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = remIsSmall } = transitivity pr1 (equalityCommutative pr)
    modIsUnique {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = (inl y) } record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) } = modUniqueLemma {rem1} {rem} {succ a} quot1 quot y x (transitivity pr1 (equalityCommutative pr))
    modIsUnique {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = (inr ()) } record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) }
    modIsUnique {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = remIsSmall1 } record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr ()) }

    transferAddition : (a b c : ℕ) → (a +N b) +N c ≡ (a +N c) +N b
    transferAddition a b c rewrite equalityCommutative (Semiring.+Associative ℕSemiring a b c) = p a b c
      where
        p : (a b c : ℕ) → a +N (b +N c) ≡ (a +N c) +N b
        p a b c = transitivity (applyEquality (a +N_) (Semiring.commutative ℕSemiring b c)) (Semiring.+Associative ℕSemiring a c b)

    divisionAlgLemma : (x b : ℕ) → x *N zero +N b ≡ b
    divisionAlgLemma x b rewrite (Semiring.productZeroRight ℕSemiring x) = refl

    divisionAlgLemma2 : (x b : ℕ) → (x ≡ b) → x *N succ zero +N zero ≡ b
    divisionAlgLemma2 x b pr rewrite (Semiring.productOneRight ℕSemiring x) = equalityCommutative (transitivity (equalityCommutative pr) (equalityCommutative (Semiring.sumZeroRight ℕSemiring x)))

    divisionAlgLemma3 : {a x : ℕ} → (p : succ a <N succ x) → (subtractionNResult.result (-N (inl p))) <N (succ x)
    divisionAlgLemma3 {a} {x} p = -NIsDecreasing {a} {succ x} p

    divisionAlgLemma4 : (p a q : ℕ) → ((p +N a *N p) +N q) +N succ a ≡ succ ((p +N a *N succ p) +N q)
    divisionAlgLemma4 p a q = ans
      where
        r   : ((p +N a *N p) +N q) +N succ a ≡ succ (((p +N a *N p) +N q) +N a)
        ans : ((p +N a *N p) +N q) +N succ a ≡ succ ((p +N a *N succ p) +N q)
        s : ((p +N a *N p) +N q) +N a ≡ (p +N a *N succ p) +N q
        t : (p +N a *N p) +N a ≡ p +N a *N succ p
        s = transitivity (transferAddition (p +N a *N p) q a) (applyEquality (λ i → i +N q) t)
        ans = identityOfIndiscernablesRight _≡_ r (applyEquality succ s)
        r = succExtracts ((p +N a *N p) +N q) a
        t = transitivity (additionNIsAssociative p (a *N p) a) (applyEquality (λ n → p +N n) (equalityCommutative (aSucB a p)))

    divisionAlg : (a : ℕ) → (b : ℕ) → divisionAlgResult a b
    divisionAlg zero = λ b → record { quot = zero ; rem = b ; pr = refl ; remIsSmall = inr refl ; quotSmall = inr (record { fst = refl ; snd = refl }) }
    divisionAlg (succ a) = rec <NWellfounded (λ n → divisionAlgResult (succ a) n) go
      where
        go : (x : ℕ) (indHyp : (y : ℕ) (y<x : y <N x) → divisionAlgResult (succ a) y) →
               divisionAlgResult (succ a) x
        go zero prop = record { quot = zero ; rem = zero ; pr = divisionAlgLemma (succ a) zero ; remIsSmall = inl (succIsPositive a) ; quotSmall = inl (succIsPositive a) }
        go (succ x) indHyp with orderIsTotal (succ a) (succ x)
        go (succ x) indHyp | inl (inl sa<sx) with indHyp (subtractionNResult.result (-N (inl sa<sx))) (divisionAlgLemma3 sa<sx)
        ... | record { quot = prevQuot ; rem = prevRem ; pr = prevPr ; remIsSmall = smallRem } = p
          where
            p : divisionAlgResult (succ a) (succ x)
            addedA : (succ a *N prevQuot +N prevRem) +N (succ a) ≡ subtractionNResult.result (-N (inl sa<sx)) +N (succ a)
            addedA' : (succ a *N prevQuot +N prevRem) +N succ a ≡ succ x
            addedA'' : (succ a *N succ prevQuot) +N prevRem ≡ succ x
            addedA''' : succ ((prevQuot +N a *N succ prevQuot) +N prevRem) ≡ succ x
            addedA''' = identityOfIndiscernablesLeft _≡_ addedA'' refl
            p = record { quot = succ prevQuot ; rem = prevRem ; pr = addedA''' ; remIsSmall = smallRem ; quotSmall = inl (succIsPositive a) }
            addedA = applyEquality (λ n → n +N succ a) prevPr
            addedA' = identityOfIndiscernablesRight _≡_ addedA (addMinus {succ a} {succ x} (inl sa<sx))
            addedA'' = identityOfIndiscernablesLeft _≡_ addedA' (divisionAlgLemma4 prevQuot a prevRem)
        go (succ x) indHyp | inr (sa=sx) = record { quot = succ zero ; rem = zero ; pr = divisionAlgLemma2 (succ a) (succ x) sa=sx ; remIsSmall = inl (succIsPositive a) ; quotSmall = inl (succIsPositive a) }
        go (succ x) indHyp | inl (inr (sx<sa)) = record { quot = zero ; rem = succ x ; pr = divisionAlgLemma (succ a) (succ x) ; remIsSmall = inl sx<sa ; quotSmall = inl (succIsPositive a) }

    data _∣_ : ℕ → ℕ → Set where
      divides : {a b : ℕ} → (res : divisionAlgResult a b) → divisionAlgResult.rem res ≡ zero → a ∣ b

    dividesEqualityLemma'' : {a b : ℕ} → (quot1 quot2 : ℕ) → (quot1 ≡ quot2) → (rem : ℕ) → (pr1 : (quot1 +N a *N quot1) +N rem ≡ b) → (pr2 : (quot2 +N a *N quot2) +N rem ≡ b) → (y : rem <N succ a) → (x1 : zero <N succ a) → record { quot = quot1 ; rem = rem ; pr = pr1 ; remIsSmall = inl y ; quotSmall = inl x1 } ≡ record { quot = quot2 ; rem = rem ; pr = pr2 ; remIsSmall = inl y ; quotSmall = inl x1}
    dividesEqualityLemma'' {a} {b} q1 .q1 refl rem pr1 pr2 y x1 rewrite reflRefl pr1 pr2 = refl

    dividesEqualityLemma' : {a b : ℕ} → (quot1 quot2 : ℕ) → (rem : ℕ) → (pr1 : (quot1 +N a *N quot1) +N rem ≡ b) → (pr2 : (quot2 +N a *N quot2) +N rem ≡ b) → (y : rem <N succ a) → (y2 : rem <N succ a) → (x1 : zero <N succ a) → record { quot = quot1 ; rem = rem ; pr = pr1 ; remIsSmall = inl y ; quotSmall = inl x1 } ≡ record { quot = quot2 ; rem = rem ; pr = pr2 ; remIsSmall = inl y2 ; quotSmall = inl x1}
    dividesEqualityLemma' {a} {b} quot1 quot2 rem pr1 pr2 y y2 x1 rewrite <NRefl y2 y = dividesEqualityLemma'' quot1 quot2 (equalityCommutative lemm'') rem pr1 pr2 y x1
      where
        lemm : (succ a) *N quot2 +N rem ≡ (succ a) *N quot1 +N rem
        lemm rewrite equalityCommutative pr1 = pr2
        lemm' : (succ a) *N quot2 ≡ (succ a) *N quot1
        lemm' = canSubtractFromEqualityRight lemm
        lemm'' : quot2 ≡ quot1
        lemm'' = productCancelsLeft (succ a) quot2 quot1 (succIsPositive a) lemm'

    dividesEqualityLemma : {a b : ℕ} → (quot1 quot2 : ℕ) → (rem1 rem2 : ℕ) → (pr1 : (quot1 +N a *N quot1) +N rem1 ≡ b) → (pr2 : (quot2 +N a *N quot2) +N rem2 ≡ b) → (rem1 ≡ rem2) → (y : rem1 <N succ a) → (y2 : rem2 <N succ a) → (x1 : zero <N succ a) → record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = inl y ; quotSmall = inl x1 } ≡ record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = inl y2 ; quotSmall = inl x1}
    dividesEqualityLemma {a} {b} quot1 quot2 rem1 rem2 pr1 pr2 remEq y y2 x1 rewrite remEq = dividesEqualityLemma' quot1 quot2 rem2 pr1 pr2 y y2 x1

    dividesEqualityPr : {a b : ℕ} → (res1 res2 : divisionAlgResult a b) → res1 ≡ res2
    dividesEqualityPr {zero} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = remIsSmall1 ; quotSmall = (inl (le x ())) } record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = remIsSmall2 ; quotSmall = quotSmall2 }
    dividesEqualityPr {zero} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = remIsSmall1 ; quotSmall = (inr (fst ,, snd)) } record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = remIsSmall2 ; quotSmall = (inl (le x ())) }
    dividesEqualityPr {zero} {b} record { quot = .0 ; rem = rem1 ; pr = pr1 ; remIsSmall = (inl (le x ())) ; quotSmall = (inr (refl ,, refl)) } record { quot = .0 ; rem = rem2 ; pr = pr2 ; remIsSmall = remIsSmall2 ; quotSmall = (inr (refl ,, refl)) }
    dividesEqualityPr {zero} {b} record { quot = .0 ; rem = rem1 ; pr = pr1 ; remIsSmall = (inr refl) ; quotSmall = (inr (refl ,, refl)) } record { quot = .0 ; rem = rem2 ; pr = pr2 ; remIsSmall = (inl (le x ())) ; quotSmall = (inr (refl ,, refl)) }
    dividesEqualityPr {zero} {.rem1} record { quot = .0 ; rem = rem1 ; pr = refl ; remIsSmall = (inr refl) ; quotSmall = (inr (refl ,, refl)) } record { quot = .0 ; rem = .rem1 ; pr = refl ; remIsSmall = (inr refl) ; quotSmall = (inr (refl ,, refl)) } = refl

    dividesEqualityPr {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = (inl y) ; quotSmall = (inl x) } record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = (inl y2) ; quotSmall = (inl x1) } rewrite <NRefl x x1 = dividesEqualityLemma quot1 quot2 rem1 rem2 pr1 pr2 remsEqual y y2 x1
      where
        remsEqual : rem1 ≡ rem2
        remsEqual = modIsUnique (record { quot = quot1 ; rem = rem1 ; pr = pr1 ; quotSmall = (inl x) ; remIsSmall = (inl y) }) (record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = (inl y2) ; quotSmall = (inl x1) })
    dividesEqualityPr {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = (inl y) ; quotSmall = (inl x) } record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = (inr ()) ; quotSmall = (inl x1) }
    dividesEqualityPr {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = (inr ()) ; quotSmall = (inl x) } record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = remIsSmall2 ; quotSmall = (inl x1) }
    dividesEqualityPr {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = remIsSmall1 ; quotSmall = (inl x) } record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = remIsSmall2 ; quotSmall = (inr (() ,, snd)) }
    dividesEqualityPr {succ a} {b} record { quot = quot1 ; rem = rem1 ; pr = pr1 ; remIsSmall = remIsSmall1 ; quotSmall = (inr (() ,, snd)) } record { quot = quot2 ; rem = rem2 ; pr = pr2 ; remIsSmall = remIsSmall2 ; quotSmall = quotSmall2 }

    dividesEquality : {a b : ℕ} → (res1 res2 : a ∣ b) → res1 ≡ res2
    dividesEquality (divides res1 x1) (divides res2 x2) rewrite dividesEqualityPr res1 res2 = applyEquality (λ i → divides res2 i) (reflRefl x1 x2)

    data notDiv : ℕ → ℕ → Set where
      doesNotDivide : {a b : ℕ} → (res : divisionAlgResult a b) → 0 <N divisionAlgResult.rem res → notDiv a b

    zeroDividesNothing : (a : ℕ) → zero ∣ succ a → False
    zeroDividesNothing a (divides record { quot = quot ; rem = rem ; pr = pr } x) = naughtE p
      where
        p : zero ≡ succ a
        p = transitivity (equalityCommutative x) pr

    twoDividesFour : succ (succ zero) ∣ succ (succ (succ (succ zero)))
    twoDividesFour = divides {(succ (succ zero))} {succ (succ (succ (succ zero)))} (record { quot = succ (succ zero) ; rem = zero ; pr = refl ; remIsSmall = inl (succIsPositive 1) ; quotSmall = inl (succIsPositive 1) }) refl

    record Prime (p : ℕ) : Set where
      field
        p>1 : 1 <N p
        pr : forall {i : ℕ} → i ∣ p → i <N p → zero <N i → i ≡ (succ zero)

    record Composite (n : ℕ) : Set where
      field
        n>1 : 1 <N n
        divisor : ℕ
        dividesN : divisor ∣ n
        divisorLessN : divisor <N n
        divisorNot1 : 1 <N divisor
        divisorPrime : Prime divisor
        noSmallerDivisors : ∀ i → i <N divisor → 1 <N i → i ∣ n → False

    notBothPrimeAndComposite : {n : ℕ} → Composite n → Prime n → False
    notBothPrimeAndComposite {n} record { n>1 = n>1 ; divisor = divisor ; dividesN = dividesN ; divisorLessN = divisorLessN ; divisorNot1 = divisorNot1 } record { p>1 = p>1 ; pr = pr } = lessImpliesNotEqual divisorNot1 (equalityCommutative div=1)
      where
        div=1 : divisor ≡ 1
        div=1 = pr {divisor} dividesN divisorLessN (orderIsTransitive (succIsPositive 0) divisorNot1)

    zeroIsNotPrime : Prime 0 → False
    zeroIsNotPrime record { p>1 = p>1 ; pr = pr } = zeroNeverGreater p>1

    oneIsNotPrime : Prime 1 → False
    oneIsNotPrime record { p>1 = (le x proof) ; pr = pr } = naughtE (equalityCommutative absurd')
      where
        absurd : x +N 1 ≡ 0
        absurd = succInjective proof
        absurd' : succ x ≡ 0
        absurd' rewrite additionNIsCommutative 1 x = absurd

    twoIsPrime : Prime 2
    Prime.p>1 twoIsPrime = succPreservesInequality (succIsPositive 0)
    Prime.pr twoIsPrime {i} i|2 i<2 0<i with orderIsTotal i (succ (succ zero))
    Prime.pr twoIsPrime {zero} i|2 i<2 (le x ()) | order
    Prime.pr twoIsPrime {succ zero} i|2 i<2 0<i | order = refl
    Prime.pr twoIsPrime {succ (succ zero)} i|2 i<2 0<i | order = exFalso (lessImpliesNotEqual {2} i<2 refl)
    Prime.pr twoIsPrime {succ (succ (succ i))} i|2 i<2 0<i | inl (inl x) = exFalso (orderIsIrreflexive i<2 (succPreservesInequality (succPreservesInequality (succIsPositive i))))
    Prime.pr twoIsPrime {succ (succ (succ i))} i|2 i<2 0<i | inl (inr twoLessThree) = exFalso (orderIsIrreflexive twoLessThree i<2)
    Prime.pr twoIsPrime {succ (succ (succ i))} i|2 i<2 0<i | inr ()

    compositeImpliesNotPrime : (m p : ℕ) → (succ zero <N m) → (m <N p) → (m ∣ p) → Prime p → False
    compositeImpliesNotPrime zero p (le x ()) _ mDivP pPrime
    compositeImpliesNotPrime (succ zero) p mLarge _ mDivP pPrime = lessImpliesNotEqual {succ zero} {succ zero} mLarge refl
    compositeImpliesNotPrime (succ (succ m)) zero _ _ mDivP ()
    compositeImpliesNotPrime (succ (succ m)) (succ zero) _ _ mDivP primeP = exFalso (oneIsNotPrime primeP)
    compositeImpliesNotPrime (succ (succ m)) (succ (succ p)) _ mLessP mDivP pPrime = false
      where
        r = succ (succ m)
        q = succ (succ p)
        rEqOne : r ≡ succ zero
        rEqOne = (Prime.pr pPrime) {r} mDivP mLessP (succIsPositive (succ m))
        false : False
        false = succIsNonzero (succInjective rEqOne)

    fourIsNotPrime : Prime 4 → False
    fourIsNotPrime = compositeImpliesNotPrime (succ (succ zero)) (succ (succ (succ (succ zero)))) (le zero refl) (le (succ zero) refl) twoDividesFour

    record hcfData (a b : ℕ) : Set where
      field
        c : ℕ
        c|a : c ∣ a
        c|b : c ∣ b
        hcf : ∀ x → x ∣ a → x ∣ b → x ∣ c

    record Coprime (a : ℕ) (b : ℕ) : Set where
      field
        hcf : hcfData a b
        hcfNot1 : 1 <N hcfData.c hcf

    record numberLessThan (n : ℕ) : Set where
      field
        a : ℕ
        a<n : a <N n
      upper : ℕ
      upper = n

    numberLessThanEquality : {n : ℕ} → (a b : numberLessThan n) → (numberLessThan.a a ≡ numberLessThan.a b) → a ≡ b
    numberLessThanEquality record { a = a ; a<n = a<n } record { a = b ; a<n = b<n } pr rewrite pr | <NRefl b<n a<n = refl

    numberLessThanOrder : (n : ℕ) → TotalOrder (numberLessThan n)
    PartialOrder._<_ (TotalOrder.order (numberLessThanOrder n)) = λ a b → (numberLessThan.a a) <N numberLessThan.a b
    PartialOrder.irreflexive (TotalOrder.order (numberLessThanOrder n)) pr = TotalOrder.irreflexive ℕTotalOrder pr
    PartialOrder.<Transitive (TotalOrder.order (numberLessThanOrder n)) pr1 pr2 = orderIsTransitive pr1 pr2
    TotalOrder.totality (numberLessThanOrder n) a b with TotalOrder.totality ℕTotalOrder (numberLessThan.a a) (numberLessThan.a b)
    TotalOrder.totality (numberLessThanOrder n) a b | inl (inl x) = inl (inl x)
    TotalOrder.totality (numberLessThanOrder n) a b | inl (inr x) = inl (inr x)
    TotalOrder.totality (numberLessThanOrder n) a b | inr x rewrite x = inr (numberLessThanEquality a b x)

    numberLessThanInject : {newMax : ℕ} → (max : ℕ) → (n : numberLessThan max) → (max <N newMax) → (numberLessThan newMax)
    numberLessThanInject max record { a = n ; a<n = n<max } max<newMax = record { a = n ; a<n = PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) n<max max<newMax }

    numberLessThanInjectComp : {max : ℕ} (a b : ℕ) → (i : numberLessThan b) → (pr : b <N a) → (pr2 : a <N max) → numberLessThanInject {max} a (numberLessThanInject {a} b i pr) pr2 ≡ numberLessThanInject {max} b i (PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) pr pr2)
    numberLessThanInjectComp {max} a b record { a = i ; a<n = i<max } b<a a<max = numberLessThanEquality _ _ refl

    allNumbersLessThanDescending : (n : ℕ) → Vec (numberLessThan n) n
    allNumbersLessThanDescending zero = []
    allNumbersLessThanDescending (succ n) = record { a = n ; a<n = le zero refl } ,- vecMap (λ i → numberLessThanInject {succ n} (numberLessThan.upper i) i (le zero refl)) (allNumbersLessThanDescending n)

    allNumbersLessThan : (n : ℕ) → Vec (numberLessThan n) n
    allNumbersLessThan n = vecRev (allNumbersLessThanDescending n)

    positiveTimes : {a b : ℕ} → (succ a *N succ b <N succ a) → False
    positiveTimes {a} {b} pr = zeroNeverGreater f'
      where
        g : succ a *N succ b <N succ a *N succ 0
        g rewrite multiplicationNIsCommutative a 1 | additionNIsCommutative a 0 = pr
        f : succ b <N succ 0
        f = cancelInequalityLeft {succ a} {succ b} g
        f' : b <N 0
        f' = canRemoveSuccFrom<N f

    biggerThanCantDivideLemma : {a b : ℕ} → (a <N b) → (b ∣ a) → a ≡ 0
    biggerThanCantDivideLemma {zero} {b} a<b b|a = refl
    biggerThanCantDivideLemma {succ a} {zero} a<b (divides record { quot = quot ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = (inl (le x ())) } refl)
    biggerThanCantDivideLemma {succ a} {zero} a<b (divides record { quot = quot ; rem = .0 ; pr = () ; remIsSmall = remIsSmall ; quotSmall = (inr x) } refl)
    biggerThanCantDivideLemma {succ a} {succ b} a<b (divides record { quot = zero ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite additionNIsCommutative (b *N zero) 0 | multiplicationNIsCommutative b 0 = exFalso (naughtE pr)
    biggerThanCantDivideLemma {succ a} {succ b} a<b (divides record { quot = (succ quot) ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite additionNIsCommutative (quot +N b *N succ quot) 0 | equalityCommutative pr = exFalso (positiveTimes {b} {quot} a<b)

    biggerThanCantDivide : {a b : ℕ} → (x : ℕ) → (TotalOrder.max ℕTotalOrder a b) <N x → (x ∣ a) → (x ∣ b) → (a ≡ 0) && (b ≡ 0)
    biggerThanCantDivide {a} {b} x pr x|a x|b with TotalOrder.totality ℕTotalOrder a b
    biggerThanCantDivide {a} {b} x pr x|a x|b | inl (inl a<b) = exFalso (zeroNeverGreater f')
      where
        f : b ≡ 0
        f = biggerThanCantDivideLemma pr x|b
        f' : a <N 0
        f' rewrite equalityCommutative f = a<b
    biggerThanCantDivide {a} {b} x pr x|a x|b | inl (inr b<a) = exFalso (zeroNeverGreater f')
      where
        f : a ≡ 0
        f = biggerThanCantDivideLemma pr x|a
        f' : b <N 0
        f' rewrite equalityCommutative f = b<a
    biggerThanCantDivide {a} {b} x pr x|a x|b | inr a=b = (transitivity a=b f ,, f)
      where
        f : b ≡ 0
        f = biggerThanCantDivideLemma pr x|b

    aDivA : (a : ℕ) → a ∣ a
    aDivA zero = divides (record { quot = 0 ; rem = 0 ; pr = equalityCommutative (oneTimesPlusZero zero) ; remIsSmall = inr refl ; quotSmall = inr (refl ,, refl) }) refl
    aDivA (succ a) = divides (record { quot = 1 ; rem = 0 ; pr = equalityCommutative (oneTimesPlusZero (succ a)) ; remIsSmall = inl (succIsPositive a) ; quotSmall = inl (succIsPositive a) }) refl

    aDivZero : (a : ℕ) → a ∣ zero
    aDivZero zero = aDivA zero
    aDivZero (succ a) = divides (record { quot = zero ; rem = zero ; pr = lemma (succ a) ; remIsSmall = inl (succIsPositive a) ; quotSmall = inl (succIsPositive a) }) refl
      where
        lemma : (b : ℕ) → b *N zero +N zero ≡ zero
        lemma b rewrite (addZeroRight (b *N zero)) = productZeroIsZeroRight b

    maxDivides : (a b : ℕ) → ((TotalOrder.max ℕTotalOrder a b) ∣ a) → (TotalOrder.max ℕTotalOrder a b) ∣ b → (((a ≡ 0) && (0 <N b)) || ((b ≡ 0) && (0 <N a))) || (a ≡ b)
    maxDivides a b max|a max|b with TotalOrder.totality ℕTotalOrder a b
    maxDivides a b max|a max|b | inl (inl a<b) = inl (inl (record { fst = gg ; snd = identityOfIndiscernablesLeft _<N_ a<b gg}))
      where
        gg : a ≡ 0
        gg = biggerThanCantDivideLemma {a} {b} a<b max|a
    maxDivides a b max|a max|b | inl (inr b<a) = inl (inr (record { fst = gg ; snd = identityOfIndiscernablesLeft _<N_ b<a gg }))
      where
        gg : b ≡ 0
        gg = biggerThanCantDivideLemma b<a max|b
    maxDivides a .a a|max b|max | inr refl = inr refl

{-
    hcfsEquivalent' : {a b : ℕ} → extensionalHCF a b → hcfData a b
    hcfData.c (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; hcfExtension = hcfExtension }) = c
    hcfData.c|a (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; hcfExtension = hcfExtension }) = c|a
    hcfData.c|b (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; hcfExtension = hcfExtension }) = c|b
    hcfData.hcf (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; hcfExtension = hcfExtension }) x x|a x|b with orderIsTotal x c
    hcfData.hcf (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; zeroCase = zeroCase ; hcfExtension = hcfExtension ; hcfExtensionIsRightLength = hIRL }) x x|a x|b | inl (inl x<c) = {!!}
      where
        xLess : numberLessThan c
        xLess = record { a = x ; a<n = x<c }
        pair : Set
        pair = Sg (numberLessThan c) (λ i → (notDiv (numberLessThan.a i) a || notDiv (numberLessThan.a i) b) || (numberLessThan.a i ∣ a) & numberLessThan.a i ∣ b & (numberLessThan.a i ∣ c))
        pr : Sg pair λ p → (lookup (MapWithDomain.map hcfExtension) xLess ≡ {!!})
        pr = MapWithDomain.lookup' hcfExtension xLess (hcfsContains {a} {b} {x} (record { c = c ; c|a = c|a ; c|b = c|b ; zeroCase = zeroCase ; hcfExtension = hcfExtension ; hcfExtensionIsRightLength = hIRL }) x<c)
    hcfData.hcf (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; zeroCase = _ ; hcfExtension = hcfExtension ; hcfExtensionIsRightLength = _ }) x x|a x|b | inl (inr c<x) = {!!}
    hcfData.hcf (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; zeroCase = _ ; hcfExtension = hcfExtension ; hcfExtensionIsRightLength = _ }) x x|a x|b | inr x=c rewrite x=c = aDivA c

    extensionalHCFEquality : {a b : ℕ} → {h1 h2 : extensionalHCF a b} → (extensionalHCF.c h1 ≡ extensionalHCF.c h2) → h1 ≡ h2
    extensionalHCFEquality {a} {b} {record { c = c1 ; c|a = c|a1 ; c|b = c|b1 ; hcfExtension = hcfExtension1 }} {record { c = c2 ; c|a = c|a2 ; c|b = c|b2 ; hcfExtension = hcfExtension2 }} pr rewrite pr = {!!}
-}

    record extendedHcf (a b : ℕ) : Set where
      field
        hcf : hcfData a b
      c : ℕ
      c = hcfData.c hcf
      field
        extended1 : ℕ
        extended2 : ℕ
        extendedProof : (a *N extended1 ≡ b *N extended2 +N c) || (a *N extended1 +N c ≡ b *N extended2)

    divEqualityLemma1 : {a b c : ℕ} → b ≡ zero → b *N c +N 0 ≡ a → a ≡ b
    divEqualityLemma1 {a} {.0} {c} refl pr = equalityCommutative pr

    divEquality : {a b : ℕ} → a ∣ b → b ∣ a → a ≡ b
    divEquality {a} {b} (divides record { quot = quotAB ; rem = .0 ; pr = prAB ; remIsSmall = _ ; quotSmall = quotSmallAB } refl) (divides record { quot = quot ; rem = .0 ; pr = pr ; remIsSmall = _ ; quotSmall = (inl x) } refl) rewrite additionNIsCommutative (b *N quot) 0 | additionNIsCommutative (a *N quotAB) 0 | equalityCommutative pr | equalityCommutative (multiplicationNIsAssociative b quot quotAB) = res
      where
        lem : {b r : ℕ} → b *N r ≡ b → (0 <N b) → r ≡ 1
        lem {zero} {r} pr ()
        lem {succ b} {zero} pr _ rewrite multiplicationNIsCommutative b 0 = exFalso (naughtE pr)
        lem {succ b} {succ zero} pr _ = refl
        lem {succ b} {succ (succ r)} pr _ rewrite multiplicationNIsCommutative b (succ (succ r)) | additionNIsCommutative (succ r) (b +N (b +N r *N b)) | additionNIsAssociative b (b +N r *N b) (succ r) | additionNIsCommutative (b +N r *N b) (succ r) = exFalso (cannotAddAndEnlarge'' {succ b} pr)
        p : quot *N quotAB ≡ 1
        p = lem prAB x
        q : quot ≡ 1
        q = _&&_.fst (productOneImpliesOperandsOne p)
        res : b *N quot ≡ b
        res rewrite q | multiplicationNIsCommutative b 1 | additionNIsCommutative b 0 = refl
    divEquality {.0} {.0} (divides record { quot = quotAB ; rem = .0 ; pr = prAB ; remIsSmall = _ ; quotSmall = quotSmallAB } refl) (divides record { quot = quot ; rem = .0 ; pr = refl ; remIsSmall = _ ; quotSmall = (inr (refl ,, snd)) } refl) = refl

    hcfWelldefined : {a b : ℕ} → (ab : hcfData a b) → (ab' : hcfData a b) → (hcfData.c ab ≡ hcfData.c ab')
    hcfWelldefined {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; hcf = hcf } record { c = c' ; c|a = c|a' ; c|b = c|b' ; hcf = hcf' } with hcf c' c|a' c|b'
    ... | c'DivC with hcf' c c|a c|b
    ... | cDivC' = divEquality cDivC' c'DivC

    reverseHCF : {a b : ℕ} → (ab : extendedHcf a b) → extendedHcf b a
    reverseHCF {a} {b} record { hcf = record { c = c ; c|a = c|a ; c|b = c|b ; hcf = hcf } ; extended1 = extended1 ; extended2 = extended2 ; extendedProof = (inl x) } = record { hcf = record { c = c ; c|a = c|b ; c|b = c|a ; hcf = λ x z z₁ → hcf x z₁ z } ; extended1 = extended2 ; extended2 = extended1 ; extendedProof = inr (equalityCommutative x) }
    reverseHCF {a} {b} record { hcf = record { c = c ; c|a = c|a ; c|b = c|b ; hcf = hcf } ; extended1 = extended1 ; extended2 = extended2 ; extendedProof = (inr x) } = record { hcf = record { c = c ; c|a = c|b ; c|b = c|a ; hcf = λ x z z₁ → hcf x z₁ z } ; extended1 = extended2 ; extended2 = extended1 ; extendedProof = inl (equalityCommutative x) }


    oneDivN : (a : ℕ) → 1 ∣ a
    oneDivN a = divides (record { quot = a ; rem = zero ; pr = pr ; remIsSmall = inl (succIsPositive zero) ; quotSmall = inl (le zero refl) }) refl
      where
        pr : (a +N zero) +N zero ≡ a
        pr rewrite addZeroRight (a +N zero) = addZeroRight a

    hcfZero : (a : ℕ) → extendedHcf zero a
    hcfZero a = record { hcf = record { c = a ; c|a = aDivZero a ; c|b = aDivA a ; hcf = λ _ _ p → p } ; extended1 = 0 ; extended2 = 1 ; extendedProof = inr (equalityCommutative (productWithOneRight a))}

    hcfOne : (a : ℕ) → extendedHcf 1 a
    hcfOne a = record { hcf = record { c = 1 ; c|a = aDivA 1 ; c|b = oneDivN a ; hcf = λ _ z _ → z } ; extended1 = 1 ; extended2 = 0 ; extendedProof = inl g }
      where
        g : 1 ≡ a *N 0 +N 1
        g rewrite multiplicationNIsCommutative a 0 = refl

    zeroIsValidRem : (a : ℕ) → (0 <N a) || (a ≡ 0)
    zeroIsValidRem zero = inr refl
    zeroIsValidRem (succ a) = inl (succIsPositive a)

    dividesBothImpliesDividesSum : {a x y : ℕ} → a ∣ x → a ∣ y → a ∣ (x +N y)
    dividesBothImpliesDividesSum {a} {x} {y} (divides record { quot = xDivA ; rem = .0 ; pr = prA ; quotSmall = qsm1 } refl) (divides record { quot = quot ; rem = .0 ; pr = pr ; quotSmall = qsm2 } refl) = divides (record { quot = xDivA +N quot ; rem = 0 ; pr = go {a} {x} {y} {xDivA} {quot} pr prA ; remIsSmall = zeroIsValidRem a ; quotSmall = (quotSmall qsm1 qsm2) }) refl
      where
        go : {a x y quot quot2 : ℕ} → (a *N quot2 +N zero ≡ y) → (a *N quot +N zero ≡ x) → a *N (quot +N quot2) +N zero ≡ x +N y
        go {a} {x} {y} {quot} {quot2} pr1 pr2 rewrite addZeroRight (a *N quot) = identityOfIndiscernablesLeft _≡_ t (equalityCommutative (addZeroRight (a *N (quot +N quot2))))
          where
            t : a *N (quot +N quot2) ≡ x +N y
            t rewrite addZeroRight (a *N quot2) = transitivity (productDistributes a quot quot2) p
              where
                s : a *N quot +N a *N quot2 ≡ x +N a *N quot2
                s = applyEquality (λ n → n +N a *N quot2) pr2
                r : x +N a *N quot2 ≡ x +N y
                r = applyEquality (λ n → x +N n) pr1
                p : a *N quot +N a *N quot2 ≡ x +N y
                p = transitivity s r
        quotSmall : ((0 <N a) || ((0 ≡ a) && (xDivA ≡ 0))) → ((0 <N a) || ((0 ≡ a) && (quot ≡ 0))) → (0 <N a) || ((0 ≡ a) && (xDivA +N quot ≡ 0))
        quotSmall (inl x1) (inl x2) = inl x1
        quotSmall (inl x1) (inr x2) = inl x1
        quotSmall (inr x1) (inl x2) = inl x2
        quotSmall (inr (a=0 ,, bl)) (inr (_ ,, bl2)) = inr (a=0 ,, ans)
          where
            ans : xDivA +N quot ≡ 0
            ans rewrite bl | bl2 = refl

    dividesBothImpliesDividesDifference : {a b c : ℕ} → a ∣ b → a ∣ c → (c<b : c <N b) → a ∣ (subtractionNResult.result (-N (inl c<b)))
    dividesBothImpliesDividesDifference {zero} {b} {.0} prab (divides record { quot = quot ; rem = .0 ; pr = refl } refl) c<b = prab
    dividesBothImpliesDividesDifference {succ a} {b} {c} (divides record { quot = bDivSA ; rem = .0 ; pr = pr } refl) (divides record { quot = cDivSA ; rem = .0 ; pr = pr2 } refl) c<b rewrite (addZeroRight (succ a *N cDivSA)) | (addZeroRight (succ a *N bDivSA)) = divides (record { quot = subtractionNResult.result bDivSA-cDivSA ; rem = 0 ; pr = identityOfIndiscernablesLeft _≡_ (identityOfIndiscernablesLeft _≡_ s (equalityCommutative q)) (equalityCommutative (addZeroRight _)) ; remIsSmall = inl (succIsPositive a) ; quotSmall = inl (succIsPositive a) }) refl
      where
        p : cDivSA <N bDivSA
        p rewrite (equalityCommutative pr2) | (equalityCommutative pr) = cancelInequalityLeft {succ a} {cDivSA} {bDivSA} c<b
        bDivSA-cDivSA : subtractionNResult cDivSA bDivSA (inl p)
        bDivSA-cDivSA = -N {cDivSA} {bDivSA} (inl p)
        la-ka = subtractionNResult.result (-N {succ a *N cDivSA} {succ a *N bDivSA} (inl (lessRespectsMultiplicationLeft cDivSA bDivSA (succ a) p (succIsPositive a))))
        q : (succ a *N (subtractionNResult.result bDivSA-cDivSA)) ≡ la-ka
        q = subtractProduct {succ a} {cDivSA} {bDivSA} (succIsPositive a) p
        s : la-ka ≡ subtractionNResult.result (-N {c} {b} (inl c<b))
        s = equivalentSubtraction (succ a *N cDivSA) b (succ a *N bDivSA) c (lessRespectsMultiplicationLeft cDivSA bDivSA (succ a) p (succIsPositive a)) c<b g
          where
            g : (succ a *N cDivSA) +N b ≡ (succ a *N bDivSA) +N c
            g rewrite equalityCommutative pr2 | equalityCommutative pr = additionNIsCommutative (cDivSA +N a *N cDivSA) (bDivSA +N a *N bDivSA)

    euclidLemma1 : {a b : ℕ} → (a<b : a <N b) → (t : ℕ) → a +N b <N t → a +N (subtractionNResult.result (-N (inl a<b))) <N t
    euclidLemma1 {zero} {b} zero<b t b<t = b<t
    euclidLemma1 {succ a} {b} sa<b t sa+b<t = identityOfIndiscernablesLeft _<N_ q (additionNIsCommutative (subtractionNResult.result (-N (inl sa<b))) (succ a))
      where
        p : b <N t
        p = orderIsTransitive (le a refl) sa+b<t
        q : (subtractionNResult.result (-N (inl sa<b))) +N succ a <N t
        q = identityOfIndiscernablesLeft _<N_ p (equalityCommutative (addMinus (inl sa<b)))

    euclidLemma2 : {a b max : ℕ} → (succ (a +N b) <N max) → b <N max
    euclidLemma2 {a} {b} {max} pr = lessTransitive {b} {succ (a +N b)} {max} (lemma a b) pr
      where
        lemma : (a b : ℕ) → b <N succ (a +N b)
        lemma a b rewrite Semiring.commutative ℕSemiring (succ a) b = addingIncreases b a

    euclidLemma3 : {a b max : ℕ} → (succ (succ (a +N b)) <N max) → succ b <N max
    euclidLemma3 {a} {b} {max} pr = euclidLemma2 {a} {succ b} {max} (identityOfIndiscernablesLeft _<N_ pr (applyEquality succ (equalityCommutative (succExtracts a b))))

    euclidLemma4 : (a b c d h : ℕ) → (sa<b : (succ a) <N b) → (pr : subtractionNResult.result (-N (inl sa<b)) *N c ≡ (succ a) *N d +N h) → b *N c ≡ (succ a) *N (d +N c) +N h
    euclidLemma4 a b zero d h sa<b pr rewrite addZeroRight d | productZeroIsZeroRight b | productZeroIsZeroRight (subtractionNResult.result (-N (inl sa<b))) = pr
    euclidLemma4 a b (succ c) d h sa<b pr rewrite subtractProduct' (succIsPositive c) sa<b = transitivity q' r'
      where
        q : (succ c) *N b ≡ succ (a +N c *N succ a) +N ((succ a) *N d +N h)
        q = moveOneSubtraction {succ (a +N c *N succ a)} {b +N c *N b} {(succ a) *N d +N h} {inl _} pr
        q' : b *N succ c ≡ succ (a +N c *N succ a) +N ((succ a) *N d +N h)
        q' rewrite multiplicationNIsCommutative b (succ c) = q
        r' : ((succ c) *N succ a) +N (((succ a) *N d) +N h) ≡ ((succ a) *N (d +N succ c)) +N h
        r' rewrite equalityCommutative (additionNIsAssociative ((succ c) *N succ a) ((succ a) *N d) h) = applyEquality (λ t → t +N h) {((succ c) *N succ a) +N ((succ a) *N d)} {(succ a) *N (d +N succ c)} (go (succ c) (succ a) d)
          where
            go' : (a b c : ℕ) → b *N a +N b *N c ≡ b *N (c +N a)
            go : (a b c : ℕ) → a *N b +N b *N c ≡ b *N (c +N a)
            go a b c rewrite multiplicationNIsCommutative a b = go' a b c
            go' a b c rewrite additionNIsCommutative (b *N a) (b *N c) = equalityCommutative (productDistributes b c a)

    euclidLemma5 : (a b c d h : ℕ) → (sa<b : (succ a) <N b) → (pr : subtractionNResult.result (-N (inl sa<b)) *N c +N h ≡ (succ a) *N d) → (succ a) *N (d +N c) ≡ b *N c +N h
    euclidLemma5 a b c d h sa<b pr with (-N (inl sa<b))
    euclidLemma5 a b zero d h sa<b pr | record { result = result ; pr = sub } rewrite addZeroRight d | productZeroIsZeroRight b | productZeroIsZeroRight result = equalityCommutative pr
    euclidLemma5 a b (succ c) d h sa<b pr | record { result = result ; pr = sub } rewrite subtractProduct' (succIsPositive c) sa<b | equalityCommutative sub = pv''
      where
        p : succ a *N d ≡ result *N succ c +N h
        p = equalityCommutative pr
        p' : a *N succ c +N succ a *N d ≡ (a *N succ c) +N ((result *N succ c) +N h)
        p' = applyEquality (λ t → a *N succ c +N t) p
        p'' : a *N succ c +N succ a *N d ≡ (a *N succ c +N result *N succ c) +N h
        p'' rewrite (additionNIsAssociative (a *N succ c) (result *N succ c) h) = p'
        p''' : a *N succ c +N succ a *N d ≡ (a +N result) *N succ c +N h
        p''' rewrite productDistributes' a result (succ c) = p''
        pv : c +N (a *N succ c +N succ a *N d) ≡ (c +N (a +N result) *N succ c) +N h
        pv rewrite additionNIsAssociative c ((a +N result) *N succ c) h = applyEquality (λ t → c +N t) p'''
        pv' : (succ c) +N (a *N succ c +N succ a *N d) ≡ succ ((c +N (a +N result) *N succ c) +N h)
        pv' = applyEquality succ pv
        pv'' : (succ a) *N (d +N succ c) ≡ succ ((c +N (a +N result) *N succ c) +N h)
        pv'' = identityOfIndiscernablesLeft _≡_ pv' (go a c d)
          where
            go : (a c d : ℕ) → (succ c) +N (a *N succ c +N ((succ a) *N d)) ≡ (succ a) *N (d +N succ c)
            go a c d rewrite equalityCommutative (additionNIsAssociative (succ c) (a *N succ c) ((succ a) *N d)) = go'
              where
                go' : (succ a) *N (succ c) +N (succ a) *N d ≡ (succ a) *N (d +N succ c)
                go' rewrite additionNIsCommutative d (succ c) = equalityCommutative (productDistributes (succ a) (succ c) d)

    euclid : (a b : ℕ) → extendedHcf a b
    euclid a b = inducted (succ a +N b) a b (a<SuccA (a +N b))
      where
        P : ℕ → Set
        P sum = ∀ (a b : ℕ) → a +N b <N sum → extendedHcf a b
        go'' : {a b : ℕ} → (maxsum : ℕ) → (a <N b) → (a +N b <N maxsum) → (∀ y → y <N maxsum → P y) → extendedHcf a b
        go'' {zero} {b} maxSum zero<b b<maxsum indHyp = hcfZero b
        go'' {1} {b} maxSum 1<b b<maxsum indHyp = hcfOne b
        go'' {succ (succ a)} {b} maxSum ssa<b ssa+b<maxsum indHyp with (indHyp (succ b) (euclidLemma3 {a} {b} {maxSum} ssa+b<maxsum)) (subtractionNResult.result (-N (inl ssa<b))) (succ (succ a)) (identityOfIndiscernablesLeft _<N_ (a<SuccA b) (equalityCommutative (addMinus (inl ssa<b))))
        go'' {succ (succ a)} {b} maxSum ssa<b ssa+b<maxsum indHyp | record { hcf = record { c = c ; c|a = c|a ; c|b = c|b ; hcf = hcf } ; extended1 = extended1 ; extended2 = extended2 ; extendedProof = inl extendedProof } = record { hcf = record { c = c ; c|a = c|b ; c|b = hcfDivB'' ; hcf = λ div prDivSSA prDivB → hcf div (dividesBothImpliesDividesDifference prDivB prDivSSA ssa<b) prDivSSA } ; extended2 = extended1; extended1 = extended2 +N extended1 ; extendedProof = inr (equalityCommutative (euclidLemma4 (succ a) b extended1 extended2 c ssa<b extendedProof)) }
          where
            hcfDivB : c ∣ ((succ (succ a)) +N (subtractionNResult.result (-N (inl ssa<b))))
            hcfDivB = dividesBothImpliesDividesSum {c} {succ (succ a)} { subtractionNResult.result (-N (inl ssa<b))} c|b c|a
            hcfDivB' : c ∣ ((subtractionNResult.result (-N (inl ssa<b))) +N (succ (succ a)))
            hcfDivB' = identityOfIndiscernablesRight _∣_ hcfDivB (additionNIsCommutative (succ (succ a)) ( subtractionNResult.result (-N (inl ssa<b))))
            hcfDivB'' : c ∣ b
            hcfDivB'' = identityOfIndiscernablesRight _∣_ hcfDivB' (addMinus (inl ssa<b))
        go'' {succ (succ a)} {b} maxSum ssa<b ssa+b<maxsum indHyp | record { hcf = record { c = c ; c|a = c|a ; c|b = c|b ; hcf = hcf } ; extended1 = extended1 ; extended2 = extended2 ; extendedProof = inr extendedProof } = record { hcf = record { c = c ; c|a = c|b ; c|b = hcfDivB'' ; hcf = λ div prDivSSA prDivB → hcf div (dividesBothImpliesDividesDifference prDivB prDivSSA ssa<b) prDivSSA } ; extended2 = extended1; extended1 = extended2 +N extended1 ; extendedProof = inl (euclidLemma5 (succ a) b extended1 extended2 c ssa<b extendedProof) }
          where
            hcfDivB : c ∣ ((succ (succ a)) +N (subtractionNResult.result (-N (inl ssa<b))))
            hcfDivB = dividesBothImpliesDividesSum {c} {succ (succ a)} { subtractionNResult.result (-N (inl ssa<b))} c|b c|a
            hcfDivB' : c ∣ ((subtractionNResult.result (-N (inl ssa<b))) +N (succ (succ a)))
            hcfDivB' = identityOfIndiscernablesRight _∣_ hcfDivB (additionNIsCommutative (succ (succ a)) (subtractionNResult.result (-N (inl ssa<b))))
            hcfDivB'' : c ∣ b
            hcfDivB'' = identityOfIndiscernablesRight _∣_ hcfDivB' (addMinus (inl ssa<b))
        go' : (maxSum a b : ℕ) → (a +N b <N maxSum) → (∀ y → y <N maxSum → P y) → extendedHcf a b
        go' maxSum a b a+b<maxsum indHyp with orderIsTotal a b
        go' maxSum a b a+b<maxsum indHyp | inl (inl a<b) = go'' maxSum a<b a+b<maxsum indHyp
        go' maxSum a b a+b<maxsum indHyp | inl (inr b<a) = reverseHCF (go'' maxSum b<a (identityOfIndiscernablesLeft _<N_ a+b<maxsum (additionNIsCommutative a b)) indHyp)
        go' maxSum a .a _ indHyp | inr refl = record { hcf = record { c = a ; c|a = aDivA a ; c|b = aDivA a ; hcf = λ _ _ z → z } ; extended1 = 0 ; extended2 = 1 ; extendedProof = inr s}
          where
            s : a *N zero +N a ≡ a *N 1
            s rewrite multiplicationNIsCommutative a zero | productWithOneRight a = refl
        go : ∀ x → (∀ y → y <N x → P y) → P x
        go maxSum indHyp = λ a b a+b<maxSum → go' maxSum a b a+b<maxSum indHyp
        inducted : ∀ x → P x
        inducted = rec <NWellfounded P go

    divisorIsSmaller : {a b : ℕ} → a ∣ succ b → succ b <N a → False
    divisorIsSmaller {a} {b} (divides record { quot = zero ; rem = .0 ; pr = pr } refl) sb<a rewrite addZeroRight (a *N zero) = go
      where
        go : False
        go rewrite productZeroIsZeroRight a = naughtE pr
    divisorIsSmaller {a} {b} (divides record { quot = (succ quot) ; rem = .0 ; pr = pr } refl) sb<a rewrite addZeroRight (a *N succ quot) = go
      where
        go : False
        go rewrite equalityCommutative pr = go'
          where
            go' : False
            go' rewrite multiplicationNIsCommutative a (succ quot) = cannotAddAndEnlarge' sb<a

    primeDivisorIs1OrP : {a p : ℕ} → (prime : Prime p) → (a ∣ p) → (a ≡ 1) || (a ≡ p)
    primeDivisorIs1OrP {zero} {zero} prime a|p = inr refl
    primeDivisorIs1OrP {zero} {succ p} prime a|p = exFalso (zeroDividesNothing p a|p)
    primeDivisorIs1OrP {succ zero} {p} prime a|p = inl refl
    primeDivisorIs1OrP {succ (succ a)} {p} prime a|p with orderIsTotal (succ (succ a)) p
    primeDivisorIs1OrP {succ (succ a)} {p} prime a|p | inl (inl ssa<p) = go p prime a|p ssa<p
      where
        go : (n : ℕ) → Prime n → succ (succ a) ∣ n → succ (succ a) <N n → (succ (succ a) ≡ 1) || (succ (succ a) ≡ p)
        go zero pr x|n n<n = exFalso (zeroIsNotPrime pr)
        go (succ zero) pr x|n n<n = exFalso (oneIsNotPrime pr)
        go (succ (succ n)) pr x|n n<n = inl ((Prime.pr pr) {succ (succ a)} x|n n<n (succIsPositive (succ a)))
    primeDivisorIs1OrP {succ (succ a)} {zero} prime a|p | inl (inr x) = exFalso (zeroIsNotPrime prime)
    primeDivisorIs1OrP {succ (succ a)} {succ p} prime a|p | inl (inr x) = exFalso (divisorIsSmaller {succ (succ a)} {p} a|p x)
    primeDivisorIs1OrP {succ (succ a)} {p} prime a|p | inr x = inr x

    hcfPrimeIsOne' : {p : ℕ} → {a : ℕ} → (Prime p) → (0 <N divisionAlgResult.rem (divisionAlg p a)) → (extendedHcf.c (euclid a p) ≡ 1) || (extendedHcf.c (euclid a p) ≡ p)
    hcfPrimeIsOne' {p} {a} pPrime pCoprimeA with euclid a p
    hcfPrimeIsOne' {p} {a} pPrime pCoprimeA | record { hcf = record { c = hcf ; c|a = hcf|a ; c|b = hcf|p ; hcf = hcfPr } } with divisionAlg p a
    hcfPrimeIsOne' {p} {a} pPrime pCoprimeA | record { hcf = record { c = hcf ; c|a = hcf|a ; c|b = hcf|p ; hcf = hcfPr } } | record { quot = quot ; rem = rem ; pr = prPDivA } with primeDivisorIs1OrP pPrime hcf|p
    hcfPrimeIsOne' {p} {a} pPrime pCoprimeA | record { hcf = record { c = hcf ; c|a = hcf|a ; c|b = hcf|p ; hcf = hcfPr } } | record { quot = quot ; rem = rem ; pr = prPDivA } | inl x = inl x
    hcfPrimeIsOne' {p} {a} pPrime pCoprimeA | record { hcf = record { c = hcf ; c|a = hcf|a ; c|b = hcf|p ; hcf = hcfPr } } | record { quot = quot ; rem = rem ; pr = prPDivA } | inr x = inr x

    divisionDecidable : (a b : ℕ) → (a ∣ b) || ((a ∣ b) → False)
    divisionDecidable zero zero = inl (aDivA zero)
    divisionDecidable zero (succ b) = inr f
      where
        f : zero ∣ succ b → False
        f (divides record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = remIsSmall } x) rewrite x = naughtE pr
    divisionDecidable (succ a) b with divisionAlg (succ a) b
    divisionDecidable (succ a) b | record { quot = quot ; rem = zero ; pr = pr ; remIsSmall = remSmall } = inl (divides (record { quot = quot ; rem = zero ; pr = pr ; remIsSmall = remSmall ; quotSmall = inl (succIsPositive a) }) refl)
    divisionDecidable (succ a) b | record { quot = b/a ; rem = succ rem ; pr = prANotDivB ; remIsSmall = inr p } = exFalso (naughtE (equalityCommutative p))
    divisionDecidable (succ a) b | record { quot = b/a ; rem = succ rem ; pr = prANotDivB ; remIsSmall = inl p } = inr f
      where
        f : (succ a) ∣ b → False
        f (divides record { quot = b/a' ; rem = .0 ; pr = pr } refl) rewrite addZeroRight ((succ a) *N b/a') = naughtE (modUniqueLemma {zero} {succ rem} {succ a} b/a' b/a (succIsPositive a) p comp')
          where
            comp : (succ a) *N b/a' ≡ (succ a) *N b/a +N succ rem
            comp = transitivity pr (equalityCommutative prANotDivB)
            comp' : (succ a) *N b/a' +N zero ≡ (succ a) *N b/a +N succ rem
            comp' rewrite addZeroRight (succ a *N b/a') = comp

    doesNotDivideImpliesNonzeroRem : (a b : ℕ) → ((a ∣ b) → False) → 0 <N divisionAlgResult.rem (divisionAlg a b)
    doesNotDivideImpliesNonzeroRem a b pr with divisionAlg a b
    doesNotDivideImpliesNonzeroRem a b pr | record { quot = quot ; rem = rem ; pr = divAlgPr ; remIsSmall = remIsSmall } with zeroIsValidRem rem
    doesNotDivideImpliesNonzeroRem a b pr | record { quot = quot ; rem = rem ; pr = divAlgPr ; remIsSmall = remIsSmall } | inl x = x
    doesNotDivideImpliesNonzeroRem a b pr | record { quot = quot ; rem = rem ; pr = divAlgPr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } | inr x = exFalso (pr aDivB)
      where
        aDivB : a ∣ b
        aDivB = divides (record { quot = quot ; rem = rem ; pr = divAlgPr ; remIsSmall = remIsSmall ; quotSmall = quotSmall }) x

    hcfPrimeIsOne : {p : ℕ} → {a : ℕ} → (Prime p) → ((p ∣ a) → False) → extendedHcf.c (euclid a p) ≡ 1
    hcfPrimeIsOne {p} {a} pPrime pr with hcfPrimeIsOne' {p} {a} pPrime (doesNotDivideImpliesNonzeroRem p a pr)
    hcfPrimeIsOne {p} {a} pPrime pr | inl x = x
    hcfPrimeIsOne {p} {a} pPrime pr | inr x with euclid a p
    hcfPrimeIsOne {p} {a} pPrime pr | inr x | record { hcf = record { c = c ; c|a = c|a ; c|b = c|b ; hcf = hcf } ; extended1 = extended1 ; extended2 = extended2 ; extendedProof = extendedProof } rewrite x = exFalso (pr c|a)

    reduceEquationMod : {a b c : ℕ} → (d : ℕ) → (a ∣ b) → (a ∣ c) → b ≡ c +N d → a ∣ d
    reduceEquationMod {a} {b} {c} 0 a|b a|c pr = aDivZero a
    reduceEquationMod {a} {b} {c} (succ d) (divides record { quot = b/a ; rem = .0 ; pr = prb/a ; remIsSmall = r1 ; quotSmall = qSm1 } refl) (divides record { quot = c/a ; rem = .0 ; pr = prc/a ; remIsSmall = r2 ; quotSmall = qSm2 } refl) b=c+d = identityOfIndiscernablesRight _∣_ a|b-c ex
      where
        c<b : c <N b
        c<b rewrite succExtracts c d | additionNIsCommutative c d = le d (equalityCommutative b=c+d)
        a|b-c : a ∣ subtractionNResult.result (-N (inl c<b))
        a|b-c = dividesBothImpliesDividesDifference (divides record { quot = b/a ; rem = 0 ; pr = prb/a ; remIsSmall = r1 ; quotSmall = qSm1 } refl) (divides record { quot = c/a ; rem = 0 ; pr = prc/a ; remIsSmall = r2 ; quotSmall = qSm2 } refl) c<b
        ex : subtractionNResult.result (-N {c} {b} (inl c<b)) ≡ subtractionNResult.result (-N {0} {succ d} (inl (succIsPositive d)))
        ex = equivalentSubtraction c (succ d) b 0 (c<b) (succIsPositive d) (equalityCommutative (identityOfIndiscernablesLeft _≡_ b=c+d (equalityCommutative (addZeroRight b))))

    primesArePrime : {p : ℕ} → {a b : ℕ} → (Prime p) → p ∣ (a *N b) → (p ∣ a) || (p ∣ b)
    primesArePrime {p} {a} {b} pPrime pr with divisionDecidable p a
    primesArePrime {p} {a} {b} pPrime pr | inl p|a = inl p|a
    primesArePrime {p} {a} {b} pPrime (divides record {quot = ab/p ; rem = .0 ; pr = p|ab ; remIsSmall = _ ; quotSmall = quotSmall } refl) | inr notp|a = inr (answer ex'')
      where
        euc : extendedHcf a p
        euc = euclid a p
        h : extendedHcf.c euc ≡ 1
        h = hcfPrimeIsOne {p} {a} pPrime notp|a
        x = extendedHcf.extended1 euc
        y = extendedHcf.extended2 euc
        extended : ((a *N x) ≡ p *N y +N extendedHcf.c euc) || (a *N x +N extendedHcf.c euc ≡ p *N y)
        extended = extendedHcf.extendedProof euc
        extended' : (a *N x ≡ p *N y +N 1) || (a *N x +N 1 ≡ p *N y)
        extended' rewrite equalityCommutative h = extended
        extended'' : ((a *N x ≡ p *N y +N 1) || (a *N x +N 1 ≡ p *N y)) → (b *N (a *N x) ≡ b *N (p *N y +N 1)) || (b *N (a *N x +N 1) ≡ b *N (p *N y))
        extended'' (inl z) = inl (applyEquality (λ t → b *N t) z)
        extended'' (inr z) = inr (applyEquality (λ t → b *N t) z)
        ex : (b *N (a *N x) ≡ b *N (p *N y +N 1)) || (b *N (a *N x +N 1) ≡ b *N (p *N y)) → ((b *N a) *N x ≡ (b *N (p *N y) +N b)) || (((b *N a) *N x +N b) ≡ b *N (p *N y))
        ex (inl z) rewrite multiplicationNIsAssociative b a x | productDistributes b (p *N y) 1 | productWithOneRight b = inl z
        ex (inr z) rewrite productDistributes b (a *N x) 1 | multiplicationNIsAssociative b a x | productWithOneRight b = inr z
        ex' : ((a *N b) *N x ≡ ((p *N y) *N b +N b)) || (((a *N b) *N x +N b) ≡ (p *N y) *N b)
        ex' rewrite multiplicationNIsCommutative a b | multiplicationNIsCommutative (p *N y) b = ex (extended'' extended')
        ex'' : ((a *N b) *N x ≡ (p *N (y *N b) +N b)) || (((a *N b) *N x +N b) ≡ p *N (y *N b))
        ex'' rewrite multiplicationNIsAssociative (p) y b = ex'
        inter1 : p ∣ (a *N b) *N x
        inter1 = divides (record {quot = ab/p *N x ; rem = 0 ; pr = g ; remIsSmall = zeroIsValidRem p ; quotSmall = qsm quotSmall}) refl
          where
            g' : p *N ab/p ≡ a *N b
            g' rewrite addZeroRight (p *N ab/p) = p|ab
            g'' : p *N (ab/p *N x) ≡ (a *N b) *N x
            g'' rewrite multiplicationNIsAssociative (p) ab/p x = applyEquality (λ t → t *N x) g'
            g : p *N (ab/p *N x) +N 0 ≡ (a *N b) *N x
            g rewrite addZeroRight (p *N (ab/p *N x)) = g''
            qsm : ((0 <N p) || ((0 ≡ p) && (ab/p ≡ 0))) → (0 <N p) || ((0 ≡ p) && (ab/p *N x ≡ 0))
            qsm (inl pr) = inl pr
            qsm (inr (pr1 ,, pr2)) = inr (pr1 ,, blah)
              where
                blah : ab/p *N x ≡ 0
                blah rewrite pr2 = refl
        inter2 : ((0 <N p) || ((0 ≡ p) && (ab/p ≡ 0))) → p ∣ (p *N (y *N b))
        inter2 (inl 0<p) = divides (record {quot = y *N b ; rem = 0 ; pr = addZeroRight (p *N (y *N b)) ; remIsSmall = zeroIsValidRem p ; quotSmall = inl 0<p }) refl
        inter2 (inr (0=p ,, ab/p=0)) = divides (record {quot = y *N b ; rem = 0 ; pr = addZeroRight (p *N (y *N b)) ; remIsSmall = zeroIsValidRem p ; quotSmall = inr (0=p ,, blah) }) refl
          where
            oneZero : (a ≡ 0) || (b ≡ 0)
            oneZero rewrite additionNIsCommutative (p *N ab/p) 0 | ab/p=0 | equalityCommutative 0=p = productZeroImpliesOperandZero (equalityCommutative p|ab)
            blah : y *N b ≡ 0
            blah with oneZero
            blah | inl x1 = exFalso (notp|a p|a)
              where
                p|a : p ∣ a
                p|a rewrite x1 = aDivZero p
            blah | inr x1 rewrite x1 = productZeroIsZeroRight y
        answer : ((a *N b) *N x ≡ (p *N (y *N b) +N b)) || (((a *N b) *N x +N b) ≡ p *N (y *N b)) → (p ∣ b)
        answer (inl z) = reduceEquationMod {p} b inter1 (inter2 quotSmall) z
        answer (inr z) = reduceEquationMod {p} b (inter2 quotSmall) inter1 (equalityCommutative z)

    primesAreBiggerThanOne : {p : ℕ} → Prime p → (1 <N p)
    primesAreBiggerThanOne {zero} record { p>1 = (le x ()) ; pr = pr }
    primesAreBiggerThanOne {succ zero} pr = exFalso (oneIsNotPrime pr)
    primesAreBiggerThanOne {succ (succ p)} pr = succPreservesInequality (succIsPositive p)

    primesAreBiggerThanZero : {p : ℕ} → Prime p → 0 <N p
    primesAreBiggerThanZero {p} pr = orderIsTransitive (succIsPositive 0) (primesAreBiggerThanOne pr)

    record notDividedByLessThan (a : ℕ) (firstPossibleDivisor : ℕ) : Set where
        field
            previousDoNotDivide : ∀ x → 1 <N x → x <N firstPossibleDivisor → x ∣ a → False

    alternativePrime : {a : ℕ} → 1 <N a → notDividedByLessThan a a → Prime a
    alternativePrime {a} 1<a record { previousDoNotDivide = previousDoNotDivide } = record { pr = pr ; p>1 = 1<a}
      where
        pr : {x : ℕ} → (x|a : x ∣ a) (x<a : x <N a) (0<x : zero <N x) → x ≡ 1
        pr {zero} _ _ (le x ())
        pr {succ zero} _ _ _ = refl
        pr {succ (succ x)} x|a x<a 0<x = exFalso (previousDoNotDivide (succ (succ x)) (succPreservesInequality (succIsPositive x)) x<a x|a)

    divisibilityTransitive : {a b c : ℕ} → a ∣ b → b ∣ c → a ∣ c
    divisibilityTransitive {a} {b} {c} (divides record { quot = b/a ; rem = .0 ; pr = prDivAB ; remIsSmall = remIsSmallAB ; quotSmall = quotSmall } refl) (divides record { quot = c/b ; rem = .0 ; pr = prDivBC ; remIsSmall = remIsSmallBC } refl) = divides record { quot = b/a *N c/b ; rem = 0 ; pr = p ; remIsSmall = zeroIsValidRem a ; quotSmall = qsm quotSmall } refl
      where
        p : a *N (b/a *N c/b) +N 0 ≡ c
        p rewrite addZeroRight (a *N (b/a *N c/b)) | addZeroRight (b *N c/b) | addZeroRight (a *N b/a) | multiplicationNIsAssociative a b/a c/b | prDivAB | prDivBC = refl
        qsm : ((0 <N a) || (0 ≡ a) && (b/a ≡ 0)) → ((0 <N a) || (0 ≡ a) && (b/a *N c/b ≡ 0))
        qsm (inl x) = inl x
        qsm (inr (p1 ,, p2)) = inr (p1 ,, blah)
          where
            blah : b/a *N c/b ≡ 0
            blah rewrite p2 = refl

    compositeOrPrimeLemma : {a b : ℕ} → notDividedByLessThan b a → a ∣ b → {i : ℕ} → (i ∣ a) → (i <N a) → (0 <N i) → i ≡ 1
    compositeOrPrimeLemma {a} {b} record { previousDoNotDivide = previousDoNotDivide } a|b {zero} i|a i<a 0<i = exFalso (lessIrreflexive 0<i)
    compositeOrPrimeLemma {a} {b} record { previousDoNotDivide = previousDoNotDivide } a|b {succ zero} i|a i<a 0<i = refl
    compositeOrPrimeLemma {a} {b} record { previousDoNotDivide = previousDoNotDivide } a|b {succ (succ i)} i|a i<a 0<i = exFalso (previousDoNotDivide (succ (succ i)) (succPreservesInequality (succIsPositive i)) i<a (divisibilityTransitive i|a a|b) )

    compositeOrPrime : (a : ℕ) → (1 <N a) → (Composite a) || (Prime a)
    compositeOrPrime a pr = go''' go''
      where
        base : notDividedByLessThan a 2
        base = record { previousDoNotDivide = λ x 1<x x<2 _ → noIntegersBetweenXAndSuccX 1 1<x x<2 }
        go : {firstPoss : ℕ} → notDividedByLessThan a firstPoss → ((notDividedByLessThan a (succ firstPoss)) || ((firstPoss ∣ a) && (firstPoss <N a))) || (firstPoss ≡ a)
        go' : (firstPoss : ℕ) → (((notDividedByLessThan a firstPoss) || (Composite a))) || (notDividedByLessThan a a)
        go'' : (notDividedByLessThan a a) || (Composite a)
        go'' with go' a
        ... | inr x = inl x
        ... | inl x = x
        go''' : ((notDividedByLessThan a a) || (Composite a)) → ((Composite a) || (Prime a))
        go''' (inl x) = inr (alternativePrime pr x)
        go''' (inr x) = inl x
        go' (zero) = inl (inl (record { previousDoNotDivide = λ x 1<x x<0 _ → zeroNeverGreater x<0 }))
        go' (succ 0) = inl (inl (record { previousDoNotDivide = λ x 1<x x<1 _ → orderIsIrreflexive x<1 1<x }))
        go' (succ (succ zero)) = inl (inl base)
        go' (succ (succ (succ firstPoss))) with go' (succ (succ firstPoss))
        go' (succ (succ (succ firstPoss))) | inl (inl x) with go {succ (succ firstPoss)} x
        go' (succ (succ (succ firstPoss))) | inl (inl x) | inl (inl x1) = inl (inl x1)
        go' (succ (succ (succ firstPoss))) | inl (inl x) | inl (inr x1) = inl (inr record { noSmallerDivisors = λ i i<ssFP 1<i i|a → notDividedByLessThan.previousDoNotDivide x i 1<i i<ssFP i|a ; n>1 = pr ; divisor = succ (succ firstPoss) ; dividesN = _&&_.fst x1 ; divisorLessN = _&&_.snd x1 ; divisorNot1 = succPreservesInequality (succIsPositive firstPoss) ; divisorPrime = record { p>1 = succPreservesInequality (succIsPositive firstPoss) ; pr = compositeOrPrimeLemma {succ (succ firstPoss)} {a} x (_&&_.fst x1) } })
        go' (succ (succ (succ firstPoss))) | inl (inl x) | inr y rewrite y = inr x
        go' (succ (succ (succ firstPoss))) | inl (inr x) = inl (inr x)
        go' (succ (succ (succ firstPoss))) | inr x = inr x

        go {zero} pr = inl (inl (record { previousDoNotDivide = λ x 1<x x<1 _ → orderIsIrreflexive x<1 1<x}))
        go {succ firstPoss} knownCoprime with orderIsTotal (succ firstPoss) a
        go {succ firstPoss} knownCoprime | inr x = inr x
        go {succ firstPoss} knownCoprime | inl (inl sFP<a) with divisionAlg (succ firstPoss) a
        go {succ firstPoss} knownCoprime | inl (inl sFP<a) | record { quot = quot ; rem = zero ; pr = pr ; remIsSmall = remIsSmall } = inl (inr record { fst = (divides (record { quot = quot ; rem = zero ; remIsSmall = remIsSmall ; pr = pr ; quotSmall = inl (succIsPositive firstPoss) }) refl) ; snd = sFP<a })
        go {succ firstPoss} knownCoprime | inl (inl sFP<a) | record { quot = quot ; rem = succ rem ; pr = pr ; remIsSmall = remIsSmall } = inl next
          where
            previous : ∀ x → 1 <N x → x <N succ firstPoss → x ∣ a → False
            previous = notDividedByLessThan.previousDoNotDivide knownCoprime
            next : notDividedByLessThan a (succ (succ firstPoss)) || (((succ firstPoss) ∣ a) && (succ firstPoss <N a))
            next with divisionAlg (succ firstPoss) a
            next | record { quot = quot ; rem = zero ; pr = pr ; remIsSmall = remIsSmall } = inr (record { fst = divides record { quot = quot ; rem = zero ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = inl (succIsPositive firstPoss) } refl ; snd = sFP<a } )
            next | record { quot = quot ; rem = succ rem ; pr = pr ; remIsSmall = remIsSmall } = inl record { previousDoNotDivide = (next' record { quot = quot ; rem = succ rem ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = inl (succIsPositive firstPoss)  } (succIsPositive rem)) }
              where
                next' : (res : divisionAlgResult (succ firstPoss) a) → (pr : 0 <N divisionAlgResult.rem res) → (x : ℕ) → 1 <N x → x <N succ (succ firstPoss) → x ∣ a → False
                next' (res) (prDiv) x 1<x x<ssFirstposs x|a with orderIsTotal x (succ firstPoss)
                next' (res) (prDiv) x 1<x x<ssFirstposs x|a | inl (inl x<sFirstPoss) = previous x 1<x x<sFirstPoss x|a
                next' (res) (prDiv) x 1<x x<ssFirstposs x|a | inl (inr sFirstPoss<x) = noIntegersBetweenXAndSuccX (succ firstPoss) sFirstPoss<x x<ssFirstposs
                next' res prDiv x 1<x x<ssFirstposs (divides res1 x1) | inr x=sFirstPoss rewrite equalityCommutative x=sFirstPoss = g
                  where
                    g : False
                    g with modIsUnique res res1
                    ... | r rewrite r = lessImpliesNotEqual prDiv (equalityCommutative x1)
        go {succ firstPoss} record { previousDoNotDivide = previousDoNotDivide } | inl (inr a<sFP) = exFalso (previousDoNotDivide a pr a<sFP (aDivA a))

    primeDivPrimeImpliesEqual : {p1 p2 : ℕ} → Prime p1 → Prime p2 → p1 ∣ p2 → p1 ≡ p2
    primeDivPrimeImpliesEqual {p1} {p2} pr1 pr2 p1|p2 with orderIsTotal p1 p2
    primeDivPrimeImpliesEqual {p1} {p2} pr1 record { p>1 = p>1 ; pr = pr } p1|p2 | inl (inl p1<p2) with pr p1|p2 p1<p2 (primesAreBiggerThanZero {p1} pr1)
    ... | p1=1 = exFalso (oneIsNotPrime contr)
      where
        contr : Prime 1
        contr rewrite p1=1 = pr1
    primeDivPrimeImpliesEqual {p1} {zero} pr1 pr2 p1|p2 | inl (inr p1>p2) = exFalso (zeroIsNotPrime pr2)
    primeDivPrimeImpliesEqual {p1} {succ p2} pr1 pr2 p1|p2 | inl (inr p1>p2) = exFalso (divisorIsSmaller p1|p2 p1>p2)
    primeDivPrimeImpliesEqual {p1} {p2} pr1 pr2 p1|p2 | inr p1=p2 = p1=p2

    mult1Lemma : {a b : ℕ} → a *N succ b ≡ 1 → (a ≡ 1) && (b ≡ 0)
    mult1Lemma {a} {b} pr = record { fst = _&&_.fst p ; snd = q}
      where
        p : (a ≡ 1) && (succ b ≡ 1)
        p = productOneImpliesOperandsOne pr
        q : b ≡ zero
        q = succInjective (_&&_.snd p)

    oneHasNoDivisors : {a : ℕ} → a ∣ 1 → a ≡ 1
    oneHasNoDivisors {a} (divides record { quot = zero ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall } refl) rewrite addZeroRight (a *N zero) | multiplicationNIsCommutative a zero | addZeroRight a = exFalso (naughtE pr)
    oneHasNoDivisors {a} (divides record { quot = (succ quot) ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall } refl) rewrite addZeroRight (a *N succ quot) = _&&_.fst (mult1Lemma pr)

    notSmallerMeansGE : {a b : ℕ} → (a <N b → False) → b ≤N a
    notSmallerMeansGE {a} {b} notA<b with orderIsTotal a b
    notSmallerMeansGE {a} {b} notA<b | inl (inl x) = exFalso (notA<b x)
    notSmallerMeansGE {a} {b} notA<b | inl (inr x) = inl x
    notSmallerMeansGE {a} {b} notA<b | inr x = inr (equalityCommutative x)
