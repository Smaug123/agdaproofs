{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Addition
open import Numbers.Naturals.Order
open import Numbers.Naturals.Multiplication
open import Numbers.Naturals.Division
open import Semirings.Definition
open import Orders.Total.Definition

module Numbers.Naturals.Naturals where

record subtractionNResult (a b : ℕ) .(p : a ≤N b) : Set where
  field
    result : ℕ
    pr : a +N result ≡ b

subtractionNWellDefined : {a b : ℕ} → {p1 p2 : a ≤N b} → (s : subtractionNResult a b p1) → (t : subtractionNResult a b p2) → (subtractionNResult.result s ≡ subtractionNResult.result t)
subtractionNWellDefined {a} {b} {inl x} {pr2} record { result = result1 ; pr = pr1 } record { result = result ; pr = pr } = canSubtractFromEqualityLeft {a} (transitivity pr1 (equalityCommutative pr))
subtractionNWellDefined {a} {.a} {inr refl} {pr2} record { result = result1 ; pr = pr1 } record { result = result2 ; pr = pr } = transitivity g' (equalityCommutative g)
  where
    g : result2 ≡ 0
    g = canSubtractFromEqualityLeft {a} {_} {0} (transitivity pr (equalityCommutative (addZeroRight a)))
    g' : result1 ≡ 0
    g' = canSubtractFromEqualityLeft {a} {_} {0} (transitivity pr1 (equalityCommutative (addZeroRight a)))

-N : {a : ℕ} → {b : ℕ} → (pr : a ≤N b) → subtractionNResult a b pr
-N {zero} {b} prAB = record { result = b ; pr = refl }
-N {succ a} {zero} (inl ())
-N {succ a} {zero} (inr ())
-N {succ a} {succ b} (inl x) with -N {a} {b} (inl (canRemoveSuccFrom<N x))
-N {succ a} {succ b} (inl x) | record { result = result ; pr = pr } = record { result = result ; pr = applyEquality succ pr }
-N {succ a} {succ b} (inr pr) = record { result = 0 ; pr = transitivity (applyEquality succ (addZeroRight a)) pr }

addOneToWeakInequality : {a b : ℕ} → (a ≤N b) → (succ a ≤N succ b)
addOneToWeakInequality {a} {b} (inl ineq) = inl (succPreservesInequality ineq)
addOneToWeakInequality {a} {.a} (inr refl) = inr refl

bumpUpSubtraction : {a b : ℕ} → (p1 : a ≤N b) → (s : subtractionNResult a b p1) → Sg (subtractionNResult (succ a) (succ b) (addOneToWeakInequality p1)) (λ n → subtractionNResult.result n ≡ subtractionNResult.result s)
bumpUpSubtraction {a} {b} a<=b record { result = result ; pr = pr } = record { result = result ; pr = applyEquality succ pr } , refl

addMinus : {a : ℕ} → {b : ℕ} → (pr : a ≤N b) → subtractionNResult.result (-N {a} {b} pr) +N a ≡ b
addMinus {zero} {zero} p = refl
addMinus {zero} {succ b} pr = applyEquality succ (addZeroRight b)
addMinus {succ a} {zero} (inl (le x ()))
addMinus {succ a} {zero} (inr ())
addMinus {succ a} {succ b} (inl x) with (-N {succ a} {succ b} (inl x))
addMinus {succ a} {succ b} (inl x) | record { result = result ; pr = pr } = transitivity (transitivity (applyEquality (_+N succ a) (transitivity (subtractionNWellDefined {p1 = inl (canRemoveSuccFrom<N x)} {p2 = inl (canRemoveSuccFrom<N x)} (record { result = subtractionNResult.result (-N (inl (canRemoveSuccFrom<N x))) ; pr = transitivity (additionNIsCommutative a _) (addMinus (inl (canRemoveSuccFrom<N x)))}) previous) (equalityCommutative t))) (additionNIsCommutative result (succ a))) pr
  where
    pr'' : (a <N b) || (a ≡ b)
    pr'' = (inl (le (_<N_.x x) (transitivity (equalityCommutative (succExtracts (_<N_.x x) a)) (succInjective (_<N_.proof x)))))
    previous : subtractionNResult a b pr''
    previous = -N pr''
    next : Sg (subtractionNResult (succ a) (succ b) (addOneToWeakInequality pr'')) λ n → subtractionNResult.result n ≡ subtractionNResult.result previous
    next = bumpUpSubtraction pr'' previous
    t : result ≡ subtractionNResult.result (underlying next)
    t = subtractionNWellDefined {succ a} {succ b} {inl x} {addOneToWeakInequality pr''} (record { result = result ; pr = pr }) (underlying next)
addMinus {succ a} {succ .a} (inr refl) = refl

addMinus' : {a b : ℕ} → (pr : a ≤N b) → a +N subtractionNResult.result (-N {a} {b} pr) ≡ b
addMinus' {a} {b} pr rewrite additionNIsCommutative a (subtractionNResult.result (-N {a} {b} pr)) = addMinus {a} {b} pr

additionPreservesInequality : {a b : ℕ} → (c : ℕ) → a <N b → a +N c <N b +N c
additionPreservesInequality {a} {b} zero prAB rewrite additionNIsCommutative a 0 | additionNIsCommutative b 0 = prAB
additionPreservesInequality {a} {b} (succ c) (le x proof) = le x (transitivity (equalityCommutative (additionNIsAssociative (succ x) a (succ c))) (applyEquality (_+N succ c) proof))

additionPreservesInequalityOnLeft : {a b : ℕ} → (c : ℕ) → a <N b → c +N a <N c +N b
additionPreservesInequalityOnLeft {a} {b} c prAB = identityOfIndiscernablesRight (λ a b → a <N b) (identityOfIndiscernablesLeft (λ a b → a <N b) (additionPreservesInequality {a} {b} c prAB) (additionNIsCommutative a c)) (additionNIsCommutative b c)

multiplyIncreases : (a : ℕ) → (b : ℕ) → succ zero <N a → zero <N b → b <N a *N b
multiplyIncreases zero b (le x ()) prB
multiplyIncreases (succ zero) b (le zero ()) prb
multiplyIncreases (succ zero) b (le (succ x) ()) prb
multiplyIncreases (succ (succ a)) (succ b) prA prb = le (b +N a *N succ b) (applyEquality succ (transitivity (Semiring.commutative ℕSemiring _ (succ b)) (transitivity (applyEquality succ (Semiring.commutative ℕSemiring b _)) (Semiring.commutative ℕSemiring _ b))))

canTimesOneOnLeft : {a b : ℕ} → (a <N b) → (a *N (succ zero)) <N b
canTimesOneOnLeft {a} {b} prAB = identityOfIndiscernablesLeft _<N_ prAB (equalityCommutative (productWithOneRight a))

canTimesOneOnRight : {a b : ℕ} → (a <N b) → a <N (b *N (succ zero))
canTimesOneOnRight {a} {b} prAB = identityOfIndiscernablesRight _<N_ prAB (equalityCommutative (productWithOneRight b))

canSwapAddOnLeftOfInequality : {a b c : ℕ} → (a +N b <N c) → (b +N a <N c)
canSwapAddOnLeftOfInequality {a} {b} {c} pr = identityOfIndiscernablesLeft _<N_ pr (additionNIsCommutative a b)

canSwapAddOnRightOfInequality : {a b c : ℕ} → (a <N b +N c) → (a <N c +N b)
canSwapAddOnRightOfInequality {a} {b} {c} pr = identityOfIndiscernablesRight _<N_ pr (additionNIsCommutative b c)

bumpDownOnRight : (a c : ℕ) → c *N succ a ≡ c *N a +N c
bumpDownOnRight a c = transitivity (multiplicationNIsCommutative c (succ a)) (transitivity refl (transitivity (additionNIsCommutative c (a *N c)) ((addingPreservesEqualityRight c (multiplicationNIsCommutative a c) ))))

succIsNonzero : {a : ℕ} → (succ a ≡ zero) → False
succIsNonzero {a} ()

lessImpliesNotEqual : {a b : ℕ} → (a <N b) → a ≡ b → False
lessImpliesNotEqual {a} {.a} prAB refl = TotalOrder.irreflexive ℕTotalOrder prAB

-NIsDecreasing : {a b : ℕ} → (prAB : succ a <N b) → subtractionNResult.result (-N (inl prAB)) <N b
-NIsDecreasing {a} {b} prAB with (-N (inl prAB))
-NIsDecreasing {a} {b} (le x proof) | record { result = result ; pr = pr } = record { x = a ; proof = pr }

sumZeroImpliesSummandsZero : {a b : ℕ} → (a +N b ≡ zero) → ((a ≡ zero) && (b ≡ zero))
sumZeroImpliesSummandsZero {zero} {zero} pr = record { fst = refl ; snd = refl }
sumZeroImpliesSummandsZero {zero} {(succ b)} pr = record { fst = refl ; snd = pr }
sumZeroImpliesSummandsZero {(succ a)} {zero} ()
sumZeroImpliesSummandsZero {(succ a)} {(succ b)} ()

productWithNonzeroZero : (a b : ℕ) → (a *N succ b ≡ zero) → a ≡ zero
productWithNonzeroZero zero b pr = refl
productWithNonzeroZero (succ a) b ()

productOneImpliesOperandsOne : {a b : ℕ} → (a *N b ≡ 1) → (a ≡ 1) && (b ≡ 1)
productOneImpliesOperandsOne {zero} {b} ()
productOneImpliesOperandsOne {succ a} {zero} pr = exFalso absurd''
  where
    absurd : zero *N (succ a) ≡ 1
    absurd' : 0 ≡ 1
    absurd'' : False
    absurd'' = succIsNonzero (equalityCommutative absurd')
    absurd = identityOfIndiscernablesLeft _≡_ pr (productZeroIsZeroRight a)
    absurd' = absurd
productOneImpliesOperandsOne {succ a} {succ b} pr = record { fst = r' ; snd = (applyEquality succ (_&&_.fst q)) }
  where
    p : b +N a *N succ b ≡ zero
    p = succInjective pr
    q : (b ≡ zero) && (a *N succ b ≡ zero)
    q = sumZeroImpliesSummandsZero p
    r : a ≡ zero
    r = productWithNonzeroZero a b (_&&_.snd q)
    r' : succ a ≡ 1
    r' = applyEquality succ r

oneTimesPlusZero : (a : ℕ) → a ≡ a *N succ zero +N zero
oneTimesPlusZero a = identityOfIndiscernablesRight _≡_ (equalityCommutative (productWithOneRight a)) (equalityCommutative (addZeroRight (a *N succ zero)))

equivalentSubtraction' : (a b c d : ℕ) → (a<c : a <N c) → (d<b : d <N b) → (subtractionNResult.result (-N {a} {c} (inl a<c))) ≡ (subtractionNResult.result (-N {d} {b} (inl d<b))) → a +N b ≡ c +N d
equivalentSubtraction' a b c d prac prdb eq with -N (inl prac)
equivalentSubtraction' a b c d prac prdb eq | record { result = result ; pr = pr } with -N (inl prdb)
equivalentSubtraction' a b c d prac prdb refl | record { result = .result ; pr = pr1 } | record { result = result ; pr = pr } rewrite (equalityCommutative pr) = go
  where
    go : a +N (d +N result) ≡ c +N d
    go rewrite (equalityCommutative pr1) = t
      where
        t : a +N (d +N result) ≡ (a +N result) +N d
        t rewrite (additionNIsAssociative a result d) = applyEquality (λ n → a +N n) (additionNIsCommutative d result)

lessThanMeansPositiveSubtr : {a b : ℕ} → (a<b : a <N b) → (subtractionNResult.result (-N (inl a<b)) ≡ 0) → False
lessThanMeansPositiveSubtr {a} {b} a<b pr with -N (inl a<b)
lessThanMeansPositiveSubtr {a} {b} a<b pr | record { result = result ; pr = sub } rewrite pr | addZeroRight a = lessImpliesNotEqual a<b sub

moveOneSubtraction : {a b c : ℕ} → {a<=b : a ≤N b} → (subtractionNResult.result (-N {a} {b} a<=b)) ≡ c → b ≡ a +N c
moveOneSubtraction {a} {b} {zero} {inl a<b} pr rewrite addZeroRight a = exFalso (lessThanMeansPositiveSubtr {a} {b} a<b pr)
moveOneSubtraction {a} {b} {succ c} {inl a<b} pr with -N (inl a<b)
moveOneSubtraction {a} {b} {succ c} {inl a<b} pr | record { result = result ; pr = sub } rewrite pr | sub = refl
moveOneSubtraction {a} {.a} {zero} {inr refl} pr = equalityCommutative (addZeroRight a)
moveOneSubtraction {a} {.a} {succ c} {inr refl} pr = identityOfIndiscernablesRight _≡_ (equalityCommutative (addZeroRight a)) (applyEquality (λ t → a +N t) pr')
  where
    selfSub : (r : ℕ) → subtractionNResult.result (-N {r} {r} (inr refl)) ≡ zero
    selfSub zero = refl
    selfSub (succ r) = refl
    pr' : 0 ≡ succ c
    pr' = transitivity (equalityCommutative (selfSub a)) pr

moveOneSubtraction' : {a b c : ℕ} → {a<=b : a ≤N b} → (b ≡ a +N c) → subtractionNResult.result (-N {a} {b} a<=b) ≡ c
moveOneSubtraction' {a} {b} {c} {inl x} pr with -N (inl x)
moveOneSubtraction' {a} {b} {c} {inl x} pr | record { result = result ; pr = pr1 } rewrite pr = canSubtractFromEqualityLeft pr1
moveOneSubtraction' {a} {b} {c} {inr x} pr with -N (inr x)
moveOneSubtraction' {a} {b} {c} {inr x} pr | record { result = result ; pr = pr1 } rewrite pr = canSubtractFromEqualityLeft pr1

equivalentSubtraction : (a b c d : ℕ) → (a<c : a <N c) → (d<b : d <N b) → a +N b ≡ c +N d → (subtractionNResult.result (-N {a} {c} (inl a<c))) ≡ (subtractionNResult.result (-N {d} {b} (inl d<b)))
equivalentSubtraction zero b c d prac (le x proof) eq with (-N (inl (le x proof)))
equivalentSubtraction zero b c d prac (le x proof) eq | record { result = result ; pr = pr } = equalityCommutative p''
  where
    p : d +N result ≡ c +N d
    p = transitivity pr eq
    p' : d +N result ≡ d +N c
    p' = transitivity p (additionNIsCommutative c d)
    p'' : result ≡ c
    p'' = canSubtractFromEqualityLeft {d} {result} {c} p'
equivalentSubtraction (succ a) b zero d (le x ()) prdb eq
equivalentSubtraction (succ a) b (succ c) d prac prdb eq with (-N (inl (canRemoveSuccFrom<N prac)))
equivalentSubtraction (succ a) b (succ c) d prac prdb eq | record { result = c-a ; pr = prc-a } with -N (inl prdb)
equivalentSubtraction (succ a) b (succ c) d prac prdb eq | record { result = c-a ; pr = prc-a } | record { result = result ; pr = pr } rewrite equalityCommutative prc-a | equalityCommutative pr | equalityCommutative (additionNIsAssociative a d result) | additionNIsCommutative (a +N c-a) d | equalityCommutative (additionNIsAssociative d a c-a) | additionNIsCommutative a d = equalityCommutative (canSubtractFromEqualityLeft eq)

leLemma : (b c : ℕ) → (b ≤N c) ≡ (b +N zero ≤N c +N zero)
leLemma b c rewrite addZeroRight c = q
  where
    q : (b ≤N c) ≡ (b +N zero ≤N c)
    q rewrite addZeroRight b = refl

lessCast : {a b c : ℕ} → (pr : a ≤N b) → (eq : a ≡ c) → c ≤N b
lessCast {a} {b} pr eq rewrite eq = pr

lessCast' : {a b c : ℕ} → (pr : a ≤N b) → (eq : b ≡ c) → a ≤N c
lessCast' {a} {b} pr eq rewrite eq = pr

subtractionCast : {a b c : ℕ} → {pr : a ≤N b} → (eq : a ≡ c) → (p : subtractionNResult a b pr) → Sg (subtractionNResult c b (lessCast pr eq)) (λ res → subtractionNResult.result p ≡ subtractionNResult.result res)
subtractionCast {a} {b} {c} {a<b} eq subt rewrite eq = (subt , refl)

subtractionCast' : {a b c : ℕ} → {pr : a ≤N b} → (eq : b ≡ c) → (p : subtractionNResult a b pr) → Sg (subtractionNResult a c (lessCast' pr eq)) (λ res → subtractionNResult.result p ≡ subtractionNResult.result res)
subtractionCast' {a} {b} {c} {a<b} eq subt rewrite eq = (subt , refl)

addToRightWeakInequality : (a : ℕ) → {b c : ℕ} → (pr : b ≤N c) → (b ≤N c +N a)
addToRightWeakInequality zero {b} {c} (inl x) rewrite (addZeroRight c) = inl x
addToRightWeakInequality (succ a) {b} {c} (inl x) = inl (TotalOrder.<Transitive ℕTotalOrder x (addingIncreases c a))
addToRightWeakInequality zero {b} {.b} (inr refl) = inr (equalityCommutative (addZeroRight b))
addToRightWeakInequality (succ a) {b} {.b} (inr refl) = inl (addingIncreases b a)

addAssocLemma : (a b c : ℕ) → (a +N b) +N c ≡ (a +N c) +N b
addAssocLemma a b c rewrite (additionNIsAssociative a b c) = g
  where
    g : a +N (b +N c) ≡ (a +N c) +N b
    g rewrite (additionNIsAssociative a c b) = applyEquality (λ t → a +N t) (additionNIsCommutative b c)

addIntoSubtraction : (a : ℕ) → {b c : ℕ} → (pr : b ≤N c) → a +N (subtractionNResult.result (-N {b} {c} pr)) ≡ subtractionNResult.result (-N {b} {c +N a} (addToRightWeakInequality a pr))
addIntoSubtraction a {b} {c} pr with (-N {b} {c} pr)
addIntoSubtraction a {b} {c} pr | record { result = c-b ; pr = prc-b } with (-N {b} {c +N a} (addToRightWeakInequality a pr))
addIntoSubtraction a {b} {c} pr | record { result = c-b ; pr = prc-b } | record { result = c+a-b ; pr = prcab } = equalityCommutative g'''
  where
    g : (b +N c+a-b) +N c-b ≡ c +N (a +N c-b)
    g rewrite (equalityCommutative (additionNIsAssociative c a c-b)) = applyEquality (λ t → t +N c-b) prcab
    g' : (b +N c-b) +N c+a-b ≡ c +N (a +N c-b)
    g' = identityOfIndiscernablesLeft _≡_ g (addAssocLemma b c+a-b c-b)
    g'' : c +N c+a-b ≡ c +N (a +N c-b)
    g'' = identityOfIndiscernablesLeft _≡_ g' (applyEquality (λ i → i +N c+a-b) prc-b)
    g''' : c+a-b ≡ a +N c-b
    g''' = canSubtractFromEqualityLeft {c} {c+a-b} {a +N c-b} g''

addStrongInequalities : {a b c d : ℕ} → (a<b : a <N b) → (c<d : c <N d) → (a +N c <N b +N d)
addStrongInequalities {zero} {zero} {c} {d} prab prcd = prcd
addStrongInequalities {zero} {succ b} {c} {d} prab prcd rewrite (additionNIsCommutative b d) = TotalOrder.<Transitive ℕTotalOrder prcd (cannotAddAndEnlarge d b)
addStrongInequalities {succ a} {zero} {c} {d} (le x ()) prcd
addStrongInequalities {succ a} {succ b} {c} {d} prab prcd = succPreservesInequality (addStrongInequalities (canRemoveSuccFrom<N prab) prcd)

addWeakInequalities : {a b c d : ℕ} → (a<=b : a ≤N b) → (c<=d : c ≤N d) → (a +N c) ≤N (b +N d)
addWeakInequalities {a} {b} {c} {d} (inl x) (inl y) = inl (addStrongInequalities x y)
addWeakInequalities {a} {b} {c} {.c} (inl x) (inr refl) = inl (additionPreservesInequality c x)
addWeakInequalities {a} {.a} {c} {d} (inr refl) (inl x) = inl (additionPreservesInequalityOnLeft a x)
addWeakInequalities {a} {.a} {c} {.c} (inr refl) (inr refl) = inr refl

addSubIntoSub : {a b c d : ℕ} → (a<b : a ≤N b) → (c<d : c ≤N d) → (subtractionNResult.result (-N {a} {b} a<b)) +N (subtractionNResult.result (-N {c} {d} c<d)) ≡ subtractionNResult.result (-N {a +N c} {b +N d} (addWeakInequalities a<b c<d))
addSubIntoSub {a}{b}{c}{d} a<b c<d with (-N {a} {b} a<b)
addSubIntoSub {a} {b} {c} {d} a<b c<d | record { result = b-a ; pr = prb-a } with (-N {c} {d} c<d)
addSubIntoSub {a} {b} {c} {d} a<b c<d | record { result = b-a ; pr = prb-a } | record { result = d-c ; pr = prd-c } with (-N {a +N c} {b +N d} (addWeakInequalities a<b c<d))
addSubIntoSub {a} {b} {c} {d} a<b c<d | record { result = b-a ; pr = prb-a } | record { result = d-c ; pr = prd-c } | record { result = b+d-a-c ; pr = pr } = equalityCommutative r
  where
    pr' : (a +N c) +N b+d-a-c ≡ (a +N b-a) +N d
    pr' rewrite prb-a = pr
    pr'' : a +N (c +N b+d-a-c) ≡ (a +N b-a) +N d
    pr'' rewrite (equalityCommutative (additionNIsAssociative a c b+d-a-c)) = pr'
    pr''' : a +N (c +N b+d-a-c) ≡ a +N (b-a +N d)
    pr''' rewrite (equalityCommutative (additionNIsAssociative a b-a d)) = pr''
    q : c +N b+d-a-c ≡ b-a +N d
    q = canSubtractFromEqualityLeft {a} pr'''
    q' : c +N b+d-a-c ≡ b-a +N (c +N d-c)
    q' rewrite prd-c = q
    q'' : c +N b+d-a-c ≡ (b-a +N c) +N d-c
    q'' rewrite additionNIsAssociative b-a c d-c = q'
    q''' : c +N b+d-a-c ≡ (c +N b-a) +N d-c
    q''' rewrite additionNIsCommutative c b-a = q''
    q'''' : c +N b+d-a-c ≡ c +N (b-a +N d-c)
    q'''' rewrite equalityCommutative (additionNIsAssociative c b-a d-c) = q'''
    r : b+d-a-c ≡ b-a +N d-c
    r = canSubtractFromEqualityLeft {c} q''''


subtractProduct : {a b c : ℕ} → (aPos : 0 <N a) → (b<c : b <N c) →
    (a *N (subtractionNResult.result (-N (inl b<c)))) ≡ subtractionNResult.result (-N {a *N b} {a *N c} (inl (lessRespectsMultiplicationLeft b c a b<c aPos)))
subtractProduct {zero} {b} {c} aPos b<c = refl
subtractProduct {succ zero} {b} {c} aPos b<c = s'
  where
    resbc = -N {b} {c} (inl b<c)
    resbc' : Sg (subtractionNResult (b +N 0 *N b) c (lessCast (inl b<c) (equalityCommutative (addZeroRight b)))) ((λ res → subtractionNResult.result resbc ≡ subtractionNResult.result res))
    resbc'' : Sg (subtractionNResult (b +N 0 *N b) (c +N 0 *N c) (lessCast' (lessCast (inl b<c) (equalityCommutative (addZeroRight b))) (equalityCommutative (addZeroRight c)))) (λ res → subtractionNResult.result (underlying resbc') ≡ subtractionNResult.result res)
    g : (rsbc' : Sg (subtractionNResult (b +N 0 *N b) c (lessCast (inl b<c) (equalityCommutative (addZeroRight b)))) (λ res → subtractionNResult.result resbc ≡ subtractionNResult.result res)) → subtractionNResult.result resbc ≡ subtractionNResult.result (underlying rsbc')
    g' : (rsbc'' : Sg (subtractionNResult (b +N 0 *N b) (c +N 0 *N c) (lessCast' (lessCast (inl b<c) (equalityCommutative (addZeroRight b))) (equalityCommutative (addZeroRight c)))) (λ res → subtractionNResult.result (underlying resbc') ≡ subtractionNResult.result res)) → subtractionNResult.result (underlying resbc') ≡ subtractionNResult.result (underlying rsbc'')
    q : subtractionNResult.result resbc ≡ subtractionNResult.result (underlying resbc'')
    r : subtractionNResult.result (underlying resbc'') ≡ subtractionNResult.result (-N {b +N 0 *N b} {c +N 0 *N c} (inl (lessRespectsMultiplicationLeft b c 1 b<c aPos)))
    s : subtractionNResult.result resbc ≡ subtractionNResult.result (-N {b +N 0 *N b} {c +N 0 *N c} (inl (lessRespectsMultiplicationLeft b c 1 b<c aPos)))
    s = transitivity q r
    s' : subtractionNResult.result resbc +N 0 ≡ subtractionNResult.result (-N {b +N 0 *N b} {c +N 0 *N c} (inl (lessRespectsMultiplicationLeft b c 1 b<c aPos)))
    s' = identityOfIndiscernablesLeft _≡_ s (equalityCommutative (addZeroRight _))
    r = subtractionNWellDefined {b +N 0 *N b} {c +N 0 *N c} {(lessCast' (lessCast (inl b<c) (equalityCommutative (addZeroRight b))) (equalityCommutative (addZeroRight c)))} {inl (lessRespectsMultiplicationLeft b c 1 b<c aPos)} (underlying resbc'') (-N {b +N 0 *N b} {c +N 0 *N c} (inl (lessRespectsMultiplicationLeft b c 1 b<c aPos)))
    g (a , b) = b
    g' (a , b) = b
    resbc'' = subtractionCast' {pr = inl (identityOfIndiscernablesLeft _<N_ b<c (equalityCommutative (addZeroRight b)))} (equalityCommutative (addZeroRight c)) (underlying resbc')
    q = transitivity {_} {_} {subtractionNResult.result resbc} {subtractionNResult.result (underlying resbc')} {subtractionNResult.result (underlying resbc'')} (g resbc') (g' resbc'')
    resbc' = subtractionCast {b} {c} {b +N 0 *N b} {inl b<c} (equalityCommutative (addZeroRight b)) resbc

subtractProduct {succ (succ a)} {b} {c} aPos b<c =
  let
    t : (succ a) *N subtractionNResult.result (-N {b} {c} (inl b<c)) ≡ subtractionNResult.result (-N {(succ a) *N b} {(succ a) *N c} (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a))))
    t = subtractProduct {succ a} {b} {c} (succIsPositive a) b<c
  in
    go t  --go t
    where
      go : (succ a) *N subtractionNResult.result (-N {b} {c} (inl b<c)) ≡ subtractionNResult.result (-N {(succ a) *N b} {(succ a) *N c} (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a)))) → (subtractionNResult.result (-N (inl b<c)) +N (subtractionNResult.result (-N (inl b<c)) +N a *N subtractionNResult.result (-N (inl b<c))) ≡ subtractionNResult.result (-N (inl (lessRespectsMultiplicationLeft b c (succ (succ a)) b<c aPos))))
      go t = transitivity {_} {_} {lhs} {middle2} {rhs} u' v
        where
          c-b = subtractionNResult.result (-N {b} {c} (inl b<c))
          lhs = c-b +N (succ a) *N c-b
          middle = subtractionNResult.result (-N {(succ a) *N b} {(succ a) *N c} (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a))))
          middle2 = subtractionNResult.result (-N {b +N (succ a *N b)} {c +N (succ a *N c)} (addWeakInequalities (inl b<c) (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a)))))
          rhs = subtractionNResult.result (-N {succ (succ a) *N b} {(succ (succ a)) *N c} (inl (lessRespectsMultiplicationLeft b c (succ (succ a)) b<c aPos)))
          lhs' : lhs ≡ c-b +N middle
          u : c-b +N middle ≡ middle2
          u' : lhs ≡ middle2
          v : middle2 ≡ rhs
          u'' : c-b +N subtractionNResult.result (-N {(succ a) *N b} {(succ a) *N c} (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a)))) ≡ rhs

          u'' rewrite equalityCommutative v = u
          u' rewrite equalityCommutative u = lhs'
          lhs' rewrite t = refl
          u = addSubIntoSub (inl b<c) (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a)))
          v = subtractionNWellDefined {succ (succ a) *N b} {succ (succ a) *N c} {addWeakInequalities (inl b<c) (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a)))} {inl (lessRespectsMultiplicationLeft b c (succ (succ a)) b<c aPos)} (-N {b +N (succ a *N b)} {c +N (succ a *N c)} (addWeakInequalities (inl b<c) (inl (lessRespectsMultiplicationLeft b c (succ a) b<c (succIsPositive a))))) (-N {(succ (succ a)) *N b} {(succ (succ a)) *N c} (inl (lessRespectsMultiplicationLeft b c (succ (succ a)) b<c aPos)))

subtractProduct' : {a b c : ℕ} → (aPos : 0 <N a) → (b<c : b <N c) →
  (subtractionNResult.result (-N (inl b<c))) *N a ≡ subtractionNResult.result (-N {a *N b} {a *N c} (inl (lessRespectsMultiplicationLeft b c a b<c aPos)))
subtractProduct' {a} aPos b<c = identityOfIndiscernablesLeft _≡_ (subtractProduct aPos b<c) (multiplicationNIsCommutative a _)

equalityDecidable : (a b : ℕ) → (a ≡ b) || ((a ≡ b) → False)
equalityDecidable zero zero = inl refl
equalityDecidable zero (succ b) = inr naughtE
equalityDecidable (succ a) zero = inr λ t → naughtE (equalityCommutative t)
equalityDecidable (succ a) (succ b) with equalityDecidable a b
equalityDecidable (succ a) (succ b) | inl x = inl (applyEquality succ x)
equalityDecidable (succ a) (succ b) | inr x = inr (λ t → x (succInjective t))

cannotAddKeepingEquality : (a b : ℕ) → (a ≡ a +N succ b) → False
cannotAddKeepingEquality zero zero pr = naughtE pr
cannotAddKeepingEquality (succ a) zero pr = cannotAddKeepingEquality a zero (succInjective pr)
cannotAddKeepingEquality zero (succ b) pr = naughtE pr
cannotAddKeepingEquality (succ a) (succ b) pr = cannotAddKeepingEquality a (succ b) (succInjective pr)

<NWellDefined' : {a b c d : ℕ} → a ≡ c → b ≡ d → a <N b → c <N d
<NWellDefined' {a} {b} {c} {d} a=c b=d a<b rewrite a=c | b=d = a<b
