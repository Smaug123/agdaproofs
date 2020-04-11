{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Numbers.Naturals.Order.WellFounded
open import Orders.WellFounded.Induction
open import Orders.Total.Definition
open import Semirings.Definition

module Numbers.Naturals.EuclideanAlgorithm where

open TotalOrder ℕTotalOrder
open Semiring ℕSemiring
open import Decidable.Lemmas ℕDecideEquality

record divisionAlgResult (a : ℕ) (b : ℕ) : Set where
  field
    quot : ℕ
    rem : ℕ
    pr : a *N quot +N rem ≡ b
    remIsSmall : (rem <N a) || (a ≡ 0)
    quotSmall : (0 <N a) || ((0 ≡ a) && (quot ≡ 0))

record divisionAlgResult' (a : ℕ) (b : ℕ) : Set where
  field
    quot : ℕ
    rem : ℕ
    .pr : a *N quot +N rem ≡ b
    remIsSmall : (rem <N' a) || (a =N' 0)
    quotSmall : (0 <N' a) || ((0 =N' a) && (quot =N' 0))

collapseDivAlgResult : {a b : ℕ} → (divisionAlgResult a b) → divisionAlgResult' a b
collapseDivAlgResult record { quot = q ; rem = r ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inl y) } = record { quot = q ; rem = r ; pr = pr ; remIsSmall = inl (<NTo<N' x) ; quotSmall = inl (<NTo<N' y) }
collapseDivAlgResult record { quot = q ; rem = r ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inr y) } = record { quot = q ; rem = r ; pr = pr ; remIsSmall = inl (<NTo<N' x) ; quotSmall = inr (collapseN (_&&_.fst y) ,, collapseN (_&&_.snd y)) }
collapseDivAlgResult record { quot = q ; rem = r ; pr = pr ; remIsSmall = (inr x) ; quotSmall = inl y } = record { quot = q ; rem = r ; pr = pr ; remIsSmall = inr (collapseN x) ; quotSmall = inl (<NTo<N' y) }
collapseDivAlgResult record { quot = q ; rem = r ; pr = pr ; remIsSmall = (inr x) ; quotSmall = inr y } = record { quot = q ; rem = r ; pr = pr ; remIsSmall = inr (collapseN x) ; quotSmall = inr (collapseN (_&&_.fst y) ,, collapseN (_&&_.snd y)) }

squashDivAlgResult : {a b : ℕ} → divisionAlgResult' a b → divisionAlgResult a b
squashDivAlgResult record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inl y) } = record { quot = quot ; rem = rem ; pr = squash pr ; remIsSmall = inl (<N'To<N x) ; quotSmall = inl (<N'To<N y) }
squashDivAlgResult record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inr y) } = record { quot = quot ; rem = rem ; pr = squash pr ; remIsSmall = inl (<N'To<N x) ; quotSmall = inr (squashN (_&&_.fst y) ,, squashN (_&&_.snd y)) }
squashDivAlgResult record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inl y) } = record { quot = quot ; rem = rem ; pr = squash pr ; remIsSmall = inr (squashN x) ; quotSmall = inl (<N'To<N y) }
squashDivAlgResult record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inr y) } = record { quot = quot ; rem = rem ; pr = squash pr ; remIsSmall = inr (squashN x) ; quotSmall = inr (squashN (_&&_.fst y) ,, squashN (_&&_.snd y)) }

squashPreservesRem : {a b : ℕ} → (p : divisionAlgResult' a b) → divisionAlgResult.rem (squashDivAlgResult p) ≡ divisionAlgResult'.rem p
squashPreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inl x₁) } = refl
squashPreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inr x₁) } = refl
squashPreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inl x₁) } = refl
squashPreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inr x₁) } = refl

squashPreservesQuot : {a b : ℕ} → (p : divisionAlgResult' a b) → divisionAlgResult.quot (squashDivAlgResult p) ≡ divisionAlgResult'.quot p
squashPreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inl x₁) } = refl
squashPreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inr x₁) } = refl
squashPreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inl x₁) } = refl
squashPreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inr x₁) } = refl

collapsePreservesRem : {a b : ℕ} → (p : divisionAlgResult a b) → divisionAlgResult'.rem (collapseDivAlgResult p) ≡ divisionAlgResult.rem p
collapsePreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inl x₁) } = refl
collapsePreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inr x₁) } = refl
collapsePreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inl x₁) } = refl
collapsePreservesRem record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inr x₁) } = refl

collapsePreservesQuot : {a b : ℕ} → (p : divisionAlgResult a b) → divisionAlgResult'.quot (collapseDivAlgResult p) ≡ divisionAlgResult.quot p
collapsePreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inl x₁) } = refl
collapsePreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inl x) ; quotSmall = (inr x₁) } = refl
collapsePreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inl x₁) } = refl
collapsePreservesQuot record { quot = quot ; rem = rem ; pr = pr ; remIsSmall = (inr x) ; quotSmall = (inr x₁) } = refl

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
    t = transitivity (equalityCommutative (Semiring.+Associative ℕSemiring p (a *N p) a)) (applyEquality (λ n → p +N n) (equalityCommutative (transitivity (multiplicationNIsCommutative a (succ p)) (transitivity (Semiring.commutative ℕSemiring a _) (applyEquality (_+N a) (multiplicationNIsCommutative p _))))))

divisionAlg : (a : ℕ) → (b : ℕ) → divisionAlgResult a b
divisionAlg zero = λ b → record { quot = zero ; rem = b ; pr = refl ; remIsSmall = inr refl ; quotSmall = inr (record { fst = refl ; snd = refl }) }
divisionAlg (succ a) = rec <NWellfounded (λ n → divisionAlgResult (succ a) n) go
  where
    go : (x : ℕ) (indHyp : (y : ℕ) (y<x : y <N x) → divisionAlgResult (succ a) y) →
            divisionAlgResult (succ a) x
    go zero prop = record { quot = zero ; rem = zero ; pr = divisionAlgLemma (succ a) zero ; remIsSmall = inl (succIsPositive a) ; quotSmall = inl (succIsPositive a) }
    go (succ x) indHyp with totality (succ a) (succ x)
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

data _∣'_ : ℕ → ℕ → Set where
  divides' : {a b : ℕ} → (res : divisionAlgResult' a b) → .(divisionAlgResult'.rem res ≡ zero) → a ∣' b

divToDiv' : {a b : ℕ} → a ∣ b → a ∣' b
divToDiv' (divides res x) = divides' (collapseDivAlgResult res) (transitivity (collapsePreservesRem res) x)

div'ToDiv : {a b : ℕ} → a ∣' b → a ∣ b
div'ToDiv (divides' res x) = divides (squashDivAlgResult res) (transitivity (squashPreservesRem res) (squashN record { eq = x }))

zeroDividesNothing : (a : ℕ) → zero ∣ succ a → False
zeroDividesNothing a (divides record { quot = quot ; rem = rem ; pr = pr } x) = naughtE p
  where
    p : zero ≡ succ a
    p = transitivity (equalityCommutative x) pr

record hcfData (a b : ℕ) : Set where
  field
    c : ℕ
    c|a : c ∣ a
    c|b : c ∣ b
    hcf : ∀ x → x ∣ a → x ∣ b → x ∣ c

positiveTimes : {a b : ℕ} → (succ a *N succ b <N succ a) → False
positiveTimes {a} {b} pr = zeroNeverGreater f'
  where
    g : succ a *N succ b <N succ a *N succ 0
    g rewrite multiplicationNIsCommutative a 1 | Semiring.commutative ℕSemiring a 0 = pr
    f : succ b <N succ 0
    f = cancelInequalityLeft {succ a} {succ b} g
    f' : b <N 0
    f' = canRemoveSuccFrom<N f

biggerThanCantDivideLemma : {a b : ℕ} → (a <N b) → (b ∣ a) → a ≡ 0
biggerThanCantDivideLemma {zero} {b} a<b b|a = refl
biggerThanCantDivideLemma {succ a} {zero} a<b (divides record { quot = quot ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = (inl (le x ())) } refl)
biggerThanCantDivideLemma {succ a} {zero} a<b (divides record { quot = quot ; rem = .0 ; pr = () ; remIsSmall = remIsSmall ; quotSmall = (inr x) } refl)
biggerThanCantDivideLemma {succ a} {succ b} a<b (divides record { quot = zero ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite Semiring.commutative ℕSemiring (b *N zero) 0 | multiplicationNIsCommutative b 0 = exFalso (naughtE pr)
biggerThanCantDivideLemma {succ a} {succ b} a<b (divides record { quot = (succ quot) ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite Semiring.commutative ℕSemiring (quot +N b *N succ quot) 0 | equalityCommutative pr = exFalso (positiveTimes {b} {quot} a<b)

biggerThanCantDivide : {a b : ℕ} → (x : ℕ) → (TotalOrder.max ℕTotalOrder a b) <N x → (x ∣ a) → (x ∣ b) → (a ≡ 0) && (b ≡ 0)
biggerThanCantDivide {a} {b} x pr x|a x|b with totality a b
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
    lemma b rewrite (Semiring.sumZeroRight ℕSemiring (b *N zero)) = Semiring.productZeroRight ℕSemiring b

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
divEquality {a} {b} (divides record { quot = quotAB ; rem = .0 ; pr = prAB ; remIsSmall = _ ; quotSmall = quotSmallAB } refl) (divides record { quot = quot ; rem = .0 ; pr = pr ; remIsSmall = _ ; quotSmall = (inl x) } refl) rewrite Semiring.commutative ℕSemiring (b *N quot) 0 | Semiring.commutative ℕSemiring (a *N quotAB) 0 | equalityCommutative pr | equalityCommutative (Semiring.*Associative ℕSemiring b quot quotAB) = res
  where
    lem : {b r : ℕ} → b *N r ≡ b → (0 <N b) → r ≡ 1
    lem {zero} {r} pr ()
    lem {succ b} {zero} pr _ rewrite multiplicationNIsCommutative b 0 = exFalso (naughtE pr)
    lem {succ b} {succ zero} pr _ = refl
    lem {succ b} {succ (succ r)} pr _ rewrite multiplicationNIsCommutative b (succ (succ r)) | Semiring.commutative ℕSemiring (succ r) (b +N (b +N r *N b)) | equalityCommutative (Semiring.+Associative ℕSemiring b (b +N r *N b) (succ r)) | Semiring.commutative ℕSemiring (b +N r *N b) (succ r) = exFalso (cannotAddAndEnlarge'' {succ b} pr)
    p : quot *N quotAB ≡ 1
    p = lem prAB x
    q : quot ≡ 1
    q = _&&_.fst (productOneImpliesOperandsOne p)
    res : b *N quot ≡ b
    res rewrite q | multiplicationNIsCommutative b 1 | Semiring.commutative ℕSemiring b 0 = refl
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
    pr rewrite Semiring.sumZeroRight ℕSemiring (a +N zero) = Semiring.sumZeroRight ℕSemiring a

hcfZero : (a : ℕ) → extendedHcf zero a
hcfZero a = record { hcf = record { c = a ; c|a = aDivZero a ; c|b = aDivA a ; hcf = λ _ _ p → p } ; extended1 = 0 ; extended2 = 1 ; extendedProof = inr (equalityCommutative (Semiring.productOneRight ℕSemiring a))}

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
    go {a} {x} {y} {quot} {quot2} pr1 pr2 rewrite Semiring.sumZeroRight ℕSemiring (a *N quot) = identityOfIndiscernablesLeft _≡_ t (equalityCommutative (Semiring.sumZeroRight ℕSemiring (a *N (quot +N quot2))))
      where
        t : a *N (quot +N quot2) ≡ x +N y
        t rewrite Semiring.sumZeroRight ℕSemiring (a *N quot2) = transitivity (Semiring.+DistributesOver* ℕSemiring a quot quot2) p
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
dividesBothImpliesDividesDifference {succ a} {b} {c} (divides record { quot = bDivSA ; rem = .0 ; pr = pr } refl) (divides record { quot = cDivSA ; rem = .0 ; pr = pr2 } refl) c<b rewrite (Semiring.sumZeroRight ℕSemiring (succ a *N cDivSA)) | (Semiring.sumZeroRight ℕSemiring (succ a *N bDivSA)) = divides (record { quot = subtractionNResult.result bDivSA-cDivSA ; rem = 0 ; pr = identityOfIndiscernablesLeft _≡_ (identityOfIndiscernablesLeft _≡_ s (equalityCommutative q)) (equalityCommutative (Semiring.sumZeroRight ℕSemiring _)) ; remIsSmall = inl (succIsPositive a) ; quotSmall = inl (succIsPositive a) }) refl
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
        g rewrite equalityCommutative pr2 | equalityCommutative pr = Semiring.commutative ℕSemiring (cDivSA +N a *N cDivSA) (bDivSA +N a *N bDivSA)

euclidLemma1 : {a b : ℕ} → (a<b : a <N b) → (t : ℕ) → a +N b <N t → a +N (subtractionNResult.result (-N (inl a<b))) <N t
euclidLemma1 {zero} {b} zero<b t b<t = b<t
euclidLemma1 {succ a} {b} sa<b t sa+b<t = identityOfIndiscernablesLeft _<N_ q (Semiring.commutative ℕSemiring (subtractionNResult.result (-N (inl sa<b))) (succ a))
  where
    p : b <N t
    p = TotalOrder.<Transitive ℕTotalOrder (le a refl) sa+b<t
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
euclidLemma4 a b zero d h sa<b pr rewrite Semiring.sumZeroRight ℕSemiring d | Semiring.productZeroRight ℕSemiring b | Semiring.productZeroRight ℕSemiring (subtractionNResult.result (-N (inl sa<b))) = pr
euclidLemma4 a b (succ c) d h sa<b pr rewrite subtractProduct' (succIsPositive c) sa<b = transitivity q' r'
  where
    q : (succ c) *N b ≡ succ (a +N c *N succ a) +N ((succ a) *N d +N h)
    q = moveOneSubtraction {succ (a +N c *N succ a)} {b +N c *N b} {(succ a) *N d +N h} {inl _} pr
    q' : b *N succ c ≡ succ (a +N c *N succ a) +N ((succ a) *N d +N h)
    q' rewrite multiplicationNIsCommutative b (succ c) = q
    r' : ((succ c) *N succ a) +N (((succ a) *N d) +N h) ≡ ((succ a) *N (d +N succ c)) +N h
    r' rewrite Semiring.+Associative ℕSemiring ((succ c) *N succ a) ((succ a) *N d) h = applyEquality (λ t → t +N h) {((succ c) *N succ a) +N ((succ a) *N d)} {(succ a) *N (d +N succ c)} (go (succ c) (succ a) d)
      where
        go' : (a b c : ℕ) → b *N a +N b *N c ≡ b *N (c +N a)
        go : (a b c : ℕ) → a *N b +N b *N c ≡ b *N (c +N a)
        go a b c rewrite multiplicationNIsCommutative a b = go' a b c
        go' a b c rewrite Semiring.commutative ℕSemiring (b *N a) (b *N c) = equalityCommutative (Semiring.+DistributesOver* ℕSemiring b c a)

euclidLemma5 : (a b c d h : ℕ) → (sa<b : (succ a) <N b) → (pr : subtractionNResult.result (-N (inl sa<b)) *N c +N h ≡ (succ a) *N d) → (succ a) *N (d +N c) ≡ b *N c +N h
euclidLemma5 a b c d h sa<b pr with (-N (inl sa<b))
euclidLemma5 a b zero d h sa<b pr | record { result = result ; pr = sub } rewrite Semiring.sumZeroRight ℕSemiring d | Semiring.productZeroRight ℕSemiring b | Semiring.productZeroRight ℕSemiring result = equalityCommutative pr
euclidLemma5 a b (succ c) d h sa<b pr | record { result = result ; pr = sub } rewrite subtractProduct' (succIsPositive c) sa<b | equalityCommutative sub = pv''
  where
    p : succ a *N d ≡ result *N succ c +N h
    p = equalityCommutative pr
    p' : a *N succ c +N succ a *N d ≡ (a *N succ c) +N ((result *N succ c) +N h)
    p' = applyEquality (λ t → a *N succ c +N t) p
    p'' : a *N succ c +N succ a *N d ≡ (a *N succ c +N result *N succ c) +N h
    p'' rewrite equalityCommutative (Semiring.+Associative ℕSemiring (a *N succ c) (result *N succ c) h) = p'
    p''' : a *N succ c +N succ a *N d ≡ (a +N result) *N succ c +N h
    p''' rewrite multiplicationNIsCommutative (a +N result) (succ c) | Semiring.+DistributesOver* ℕSemiring (succ c) a result | multiplicationNIsCommutative (succ c) a | multiplicationNIsCommutative (succ c) result = p''
    pv : c +N (a *N succ c +N succ a *N d) ≡ (c +N (a +N result) *N succ c) +N h
    pv rewrite equalityCommutative (Semiring.+Associative ℕSemiring c ((a +N result) *N succ c) h) = applyEquality (λ t → c +N t) p'''
    pv' : (succ c) +N (a *N succ c +N succ a *N d) ≡ succ ((c +N (a +N result) *N succ c) +N h)
    pv' = applyEquality succ pv
    pv'' : (succ a) *N (d +N succ c) ≡ succ ((c +N (a +N result) *N succ c) +N h)
    pv'' = identityOfIndiscernablesLeft _≡_ pv' (go a c d)
      where
        go : (a c d : ℕ) → (succ c) +N (a *N succ c +N ((succ a) *N d)) ≡ (succ a) *N (d +N succ c)
        go a c d rewrite Semiring.+Associative ℕSemiring (succ c) (a *N succ c) ((succ a) *N d) = go'
          where
            go' : (succ a) *N (succ c) +N (succ a) *N d ≡ (succ a) *N (d +N succ c)
            go' rewrite Semiring.commutative ℕSemiring d (succ c) = equalityCommutative (Semiring.+DistributesOver* ℕSemiring (succ a) (succ c) d)

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
        hcfDivB' = identityOfIndiscernablesRight _∣_ hcfDivB (Semiring.commutative ℕSemiring (succ (succ a)) ( subtractionNResult.result (-N (inl ssa<b))))
        hcfDivB'' : c ∣ b
        hcfDivB'' = identityOfIndiscernablesRight _∣_ hcfDivB' (addMinus (inl ssa<b))
    go'' {succ (succ a)} {b} maxSum ssa<b ssa+b<maxsum indHyp | record { hcf = record { c = c ; c|a = c|a ; c|b = c|b ; hcf = hcf } ; extended1 = extended1 ; extended2 = extended2 ; extendedProof = inr extendedProof } = record { hcf = record { c = c ; c|a = c|b ; c|b = hcfDivB'' ; hcf = λ div prDivSSA prDivB → hcf div (dividesBothImpliesDividesDifference prDivB prDivSSA ssa<b) prDivSSA } ; extended2 = extended1; extended1 = extended2 +N extended1 ; extendedProof = inl (euclidLemma5 (succ a) b extended1 extended2 c ssa<b extendedProof) }
      where
        hcfDivB : c ∣ ((succ (succ a)) +N (subtractionNResult.result (-N (inl ssa<b))))
        hcfDivB = dividesBothImpliesDividesSum {c} {succ (succ a)} { subtractionNResult.result (-N (inl ssa<b))} c|b c|a
        hcfDivB' : c ∣ ((subtractionNResult.result (-N (inl ssa<b))) +N (succ (succ a)))
        hcfDivB' = identityOfIndiscernablesRight _∣_ hcfDivB (Semiring.commutative ℕSemiring (succ (succ a)) (subtractionNResult.result (-N (inl ssa<b))))
        hcfDivB'' : c ∣ b
        hcfDivB'' = identityOfIndiscernablesRight _∣_ hcfDivB' (addMinus (inl ssa<b))
    go' : (maxSum a b : ℕ) → (a +N b <N maxSum) → (∀ y → y <N maxSum → P y) → extendedHcf a b
    go' maxSum a b a+b<maxsum indHyp with totality a b
    go' maxSum a b a+b<maxsum indHyp | inl (inl a<b) = go'' maxSum a<b a+b<maxsum indHyp
    go' maxSum a b a+b<maxsum indHyp | inl (inr b<a) = reverseHCF (go'' maxSum b<a (identityOfIndiscernablesLeft _<N_ a+b<maxsum (Semiring.commutative ℕSemiring a b)) indHyp)
    go' maxSum a .a _ indHyp | inr refl = record { hcf = record { c = a ; c|a = aDivA a ; c|b = aDivA a ; hcf = λ _ _ z → z } ; extended1 = 0 ; extended2 = 1 ; extendedProof = inr s}
      where
        s : a *N zero +N a ≡ a *N 1
        s rewrite multiplicationNIsCommutative a zero | Semiring.productOneRight ℕSemiring a = refl
    go : ∀ x → (∀ y → y <N x → P y) → P x
    go maxSum indHyp = λ a b a+b<maxSum → go' maxSum a b a+b<maxSum indHyp
    inducted : ∀ x → P x
    inducted = rec <NWellfounded P go

divOneImpliesOne : {a : ℕ} → a ∣ 1 → a ≡ 1
divOneImpliesOne {zero} a|1 = exFalso (zeroDividesNothing _ a|1)
divOneImpliesOne {succ zero} a|1 = refl
divOneImpliesOne {succ (succ a)} (divides record { quot = zero ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite Semiring.sumZeroRight ℕSemiring (a *N zero) | multiplicationNIsCommutative a 0 = exFalso (naughtE pr)
divOneImpliesOne {succ (succ a)} (divides record { quot = (succ quot) ; rem = .0 ; pr = pr ; remIsSmall = remIsSmall ; quotSmall = quotSmall } refl) rewrite Semiring.commutative ℕSemiring quot (succ (quot +N a *N succ quot)) = exFalso (naughtE (equalityCommutative (succInjective pr)))
