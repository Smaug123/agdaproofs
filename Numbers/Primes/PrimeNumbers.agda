{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Numbers.Naturals.Order.WellFounded
open import Numbers.Naturals.WithK
open import WellFoundedInduction
open import KeyValue.KeyValue
open import Orders
open import Vectors
open import Maybe
open import WithK
open import Semirings.Definition
open import Numbers.Naturals.EuclideanAlgorithm

module Numbers.Primes.PrimeNumbers where

open TotalOrder ℕTotalOrder
open Semiring ℕSemiring

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
    div=1 = pr {divisor} dividesN divisorLessN (TotalOrder.<Transitive ℕTotalOrder (succIsPositive 0) divisorNot1)

zeroIsNotPrime : Prime 0 → False
zeroIsNotPrime record { p>1 = p>1 ; pr = pr } = zeroNeverGreater p>1

oneIsNotPrime : Prime 1 → False
oneIsNotPrime record { p>1 = (le x proof) ; pr = pr } = naughtE (equalityCommutative absurd')
  where
    absurd : x +N 1 ≡ 0
    absurd = succInjective proof
    absurd' : succ x ≡ 0
    absurd' rewrite Semiring.commutative ℕSemiring 1 x = absurd

twoIsPrime : Prime 2
Prime.p>1 twoIsPrime = succPreservesInequality (succIsPositive 0)
Prime.pr twoIsPrime {i} i|2 i<2 0<i with totality i (succ (succ zero))
Prime.pr twoIsPrime {zero} i|2 i<2 (le x ()) | order
Prime.pr twoIsPrime {succ zero} i|2 i<2 0<i | order = refl
Prime.pr twoIsPrime {succ (succ zero)} i|2 i<2 0<i | order = exFalso (lessImpliesNotEqual {2} i<2 refl)
Prime.pr twoIsPrime {succ (succ (succ i))} i|2 i<2 0<i | inl (inl x) = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder i<2 (succPreservesInequality (succPreservesInequality (succIsPositive i)))))
Prime.pr twoIsPrime {succ (succ (succ i))} i|2 i<2 0<i | inl (inr twoLessThree) = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder twoLessThree i<2))
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
PartialOrder.<Transitive (TotalOrder.order (numberLessThanOrder n)) pr1 pr2 = TotalOrder.<Transitive ℕTotalOrder pr1 pr2
TotalOrder.totality (numberLessThanOrder n) a b with totality (numberLessThan.a a) (numberLessThan.a b)
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

maxDivides : (a b : ℕ) → ((TotalOrder.max ℕTotalOrder a b) ∣ a) → (TotalOrder.max ℕTotalOrder a b) ∣ b → (((a ≡ 0) && (0 <N b)) || ((b ≡ 0) && (0 <N a))) || (a ≡ b)
maxDivides a b max|a max|b with totality a b
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
hcfData.hcf (hcfsEquivalent' {a} {b} record { c = c ; c|a = c|a ; c|b = c|b ; hcfExtension = hcfExtension }) x x|a x|b with totality ℕTotalOrder x c
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

divisorIsSmaller : {a b : ℕ} → a ∣ succ b → succ b <N a → False
divisorIsSmaller {a} {b} (divides record { quot = zero ; rem = .0 ; pr = pr } refl) sb<a rewrite Semiring.sumZeroRight ℕSemiring (a *N zero) = go
  where
    go : False
    go rewrite Semiring.productZeroRight ℕSemiring a = naughtE pr
divisorIsSmaller {a} {b} (divides record { quot = (succ quot) ; rem = .0 ; pr = pr } refl) sb<a rewrite Semiring.sumZeroRight ℕSemiring (a *N succ quot) = go
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
primeDivisorIs1OrP {succ (succ a)} {p} prime a|p with totality (succ (succ a)) p
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
    f (divides record { quot = b/a' ; rem = .0 ; pr = pr } refl) rewrite Semiring.sumZeroRight ℕSemiring ((succ a) *N b/a') = naughtE (modUniqueLemma {zero} {succ rem} {succ a} b/a' b/a (succIsPositive a) p comp')
      where
        comp : (succ a) *N b/a' ≡ (succ a) *N b/a +N succ rem
        comp = transitivity pr (equalityCommutative prANotDivB)
        comp' : (succ a) *N b/a' +N zero ≡ (succ a) *N b/a +N succ rem
        comp' rewrite Semiring.sumZeroRight ℕSemiring (succ a *N b/a') = comp

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
    c<b rewrite succExtracts c d | Semiring.commutative ℕSemiring c d = le d (equalityCommutative b=c+d)
    a|b-c : a ∣ subtractionNResult.result (-N (inl c<b))
    a|b-c = dividesBothImpliesDividesDifference (divides record { quot = b/a ; rem = 0 ; pr = prb/a ; remIsSmall = r1 ; quotSmall = qSm1 } refl) (divides record { quot = c/a ; rem = 0 ; pr = prc/a ; remIsSmall = r2 ; quotSmall = qSm2 } refl) c<b
    ex : subtractionNResult.result (-N {c} {b} (inl c<b)) ≡ subtractionNResult.result (-N {0} {succ d} (inl (succIsPositive d)))
    ex = equivalentSubtraction c (succ d) b 0 (c<b) (succIsPositive d) (equalityCommutative (identityOfIndiscernablesLeft _≡_ b=c+d (equalityCommutative (Semiring.sumZeroRight ℕSemiring b))))

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
    ex (inl z) rewrite Semiring.*Associative ℕSemiring b a x | Semiring.+DistributesOver* ℕSemiring b (p *N y) 1 | Semiring.productOneRight ℕSemiring b = inl z
    ex (inr z) rewrite Semiring.+DistributesOver* ℕSemiring b (a *N x) 1 | Semiring.*Associative ℕSemiring b a x | Semiring.productOneRight ℕSemiring b = inr z
    ex' : ((a *N b) *N x ≡ ((p *N y) *N b +N b)) || (((a *N b) *N x +N b) ≡ (p *N y) *N b)
    ex' rewrite multiplicationNIsCommutative a b | multiplicationNIsCommutative (p *N y) b = ex (extended'' extended')
    ex'' : ((a *N b) *N x ≡ (p *N (y *N b) +N b)) || (((a *N b) *N x +N b) ≡ p *N (y *N b))
    ex'' rewrite Semiring.*Associative ℕSemiring (p) y b = ex'
    inter1 : p ∣ (a *N b) *N x
    inter1 = divides (record {quot = ab/p *N x ; rem = 0 ; pr = g ; remIsSmall = zeroIsValidRem p ; quotSmall = qsm quotSmall}) refl
      where
        g' : p *N ab/p ≡ a *N b
        g' rewrite Semiring.sumZeroRight ℕSemiring (p *N ab/p) = p|ab
        g'' : p *N (ab/p *N x) ≡ (a *N b) *N x
        g'' rewrite Semiring.*Associative ℕSemiring (p) ab/p x = applyEquality (λ t → t *N x) g'
        g : p *N (ab/p *N x) +N 0 ≡ (a *N b) *N x
        g rewrite Semiring.sumZeroRight ℕSemiring (p *N (ab/p *N x)) = g''
        qsm : ((0 <N p) || ((0 ≡ p) && (ab/p ≡ 0))) → (0 <N p) || ((0 ≡ p) && (ab/p *N x ≡ 0))
        qsm (inl pr) = inl pr
        qsm (inr (pr1 ,, pr2)) = inr (pr1 ,, blah)
          where
            blah : ab/p *N x ≡ 0
            blah rewrite pr2 = refl
    inter2 : ((0 <N p) || ((0 ≡ p) && (ab/p ≡ 0))) → p ∣ (p *N (y *N b))
    inter2 (inl 0<p) = divides (record {quot = y *N b ; rem = 0 ; pr = Semiring.sumZeroRight ℕSemiring (p *N (y *N b)) ; remIsSmall = zeroIsValidRem p ; quotSmall = inl 0<p }) refl
    inter2 (inr (0=p ,, ab/p=0)) = divides (record {quot = y *N b ; rem = 0 ; pr = Semiring.sumZeroRight ℕSemiring (p *N (y *N b)) ; remIsSmall = zeroIsValidRem p ; quotSmall = inr (0=p ,, blah) }) refl
      where
        oneZero : (a ≡ 0) || (b ≡ 0)
        oneZero rewrite Semiring.commutative ℕSemiring (p *N ab/p) 0 | ab/p=0 | equalityCommutative 0=p = productZeroImpliesOperandZero (equalityCommutative p|ab)
        blah : y *N b ≡ 0
        blah with oneZero
        blah | inl x1 = exFalso (notp|a p|a)
          where
            p|a : p ∣ a
            p|a rewrite x1 = aDivZero p
        blah | inr x1 rewrite x1 = Semiring.productZeroRight ℕSemiring y
    answer : ((a *N b) *N x ≡ (p *N (y *N b) +N b)) || (((a *N b) *N x +N b) ≡ p *N (y *N b)) → (p ∣ b)
    answer (inl z) = reduceEquationMod {p} b inter1 (inter2 quotSmall) z
    answer (inr z) = reduceEquationMod {p} b (inter2 quotSmall) inter1 (equalityCommutative z)

primesAreBiggerThanOne : {p : ℕ} → Prime p → (1 <N p)
primesAreBiggerThanOne {zero} record { p>1 = (le x ()) ; pr = pr }
primesAreBiggerThanOne {succ zero} pr = exFalso (oneIsNotPrime pr)
primesAreBiggerThanOne {succ (succ p)} pr = succPreservesInequality (succIsPositive p)

primesAreBiggerThanZero : {p : ℕ} → Prime p → 0 <N p
primesAreBiggerThanZero {p} pr = TotalOrder.<Transitive ℕTotalOrder (succIsPositive 0) (primesAreBiggerThanOne pr)

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
    p rewrite Semiring.sumZeroRight ℕSemiring (a *N (b/a *N c/b)) | Semiring.sumZeroRight ℕSemiring (b *N c/b) | Semiring.sumZeroRight ℕSemiring (a *N b/a) | Semiring.*Associative ℕSemiring a b/a c/b | prDivAB | prDivBC = refl
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
    go' (succ 0) = inl (inl (record { previousDoNotDivide = λ x 1<x x<1 _ → TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder x<1 1<x) }))
    go' (succ (succ zero)) = inl (inl base)
    go' (succ (succ (succ firstPoss))) with go' (succ (succ firstPoss))
    go' (succ (succ (succ firstPoss))) | inl (inl x) with go {succ (succ firstPoss)} x
    go' (succ (succ (succ firstPoss))) | inl (inl x) | inl (inl x1) = inl (inl x1)
    go' (succ (succ (succ firstPoss))) | inl (inl x) | inl (inr x1) = inl (inr record { noSmallerDivisors = λ i i<ssFP 1<i i|a → notDividedByLessThan.previousDoNotDivide x i 1<i i<ssFP i|a ; n>1 = pr ; divisor = succ (succ firstPoss) ; dividesN = _&&_.fst x1 ; divisorLessN = _&&_.snd x1 ; divisorNot1 = succPreservesInequality (succIsPositive firstPoss) ; divisorPrime = record { p>1 = succPreservesInequality (succIsPositive firstPoss) ; pr = compositeOrPrimeLemma {succ (succ firstPoss)} {a} x (_&&_.fst x1) } })
    go' (succ (succ (succ firstPoss))) | inl (inl x) | inr y rewrite y = inr x
    go' (succ (succ (succ firstPoss))) | inl (inr x) = inl (inr x)
    go' (succ (succ (succ firstPoss))) | inr x = inr x

    go {zero} pr = inl (inl (record { previousDoNotDivide = λ x 1<x x<1 _ → irreflexive (<Transitive x<1 1<x)}))
    go {succ firstPoss} knownCoprime with totality (succ firstPoss) a
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
            next' (res) (prDiv) x 1<x x<ssFirstposs x|a with totality x (succ firstPoss)
            next' (res) (prDiv) x 1<x x<ssFirstposs x|a | inl (inl x<sFirstPoss) = previous x 1<x x<sFirstPoss x|a
            next' (res) (prDiv) x 1<x x<ssFirstposs x|a | inl (inr sFirstPoss<x) = noIntegersBetweenXAndSuccX (succ firstPoss) sFirstPoss<x x<ssFirstposs
            next' res prDiv x 1<x x<ssFirstposs (divides res1 x1) | inr x=sFirstPoss rewrite equalityCommutative x=sFirstPoss = g
              where
                g : False
                g with modIsUnique res res1
                ... | r rewrite r = lessImpliesNotEqual prDiv (equalityCommutative x1)
    go {succ firstPoss} record { previousDoNotDivide = previousDoNotDivide } | inl (inr a<sFP) = exFalso (previousDoNotDivide a pr a<sFP (aDivA a))

primeDivPrimeImpliesEqual : {p1 p2 : ℕ} → Prime p1 → Prime p2 → p1 ∣ p2 → p1 ≡ p2
primeDivPrimeImpliesEqual {p1} {p2} pr1 pr2 p1|p2 with totality p1 p2
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
oneHasNoDivisors {a} (divides record { quot = zero ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall } refl) rewrite Semiring.sumZeroRight ℕSemiring (a *N zero) | multiplicationNIsCommutative a zero | Semiring.sumZeroRight ℕSemiring a = exFalso (naughtE pr)
oneHasNoDivisors {a} (divides record { quot = (succ quot) ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall } refl) rewrite Semiring.sumZeroRight ℕSemiring (a *N succ quot) = _&&_.fst (mult1Lemma pr)

notSmallerMeansGE : {a b : ℕ} → (a <N b → False) → b ≤N a
notSmallerMeansGE {a} {b} notA<b with totality a b
notSmallerMeansGE {a} {b} notA<b | inl (inl x) = exFalso (notA<b x)
notSmallerMeansGE {a} {b} notA<b | inl (inr x) = inl x
notSmallerMeansGE {a} {b} notA<b | inr x = inr (equalityCommutative x)
