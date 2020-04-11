{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Semirings.Definition
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Semiring
open import Orders.Total.Definition
open import Orders.Partial.Definition

module Numbers.Naturals.Order where
open Semiring ℕSemiring
open import Decidable.Lemmas ℕDecideEquality

private
  infix 5 _<NLogical_
  _<NLogical_ : ℕ → ℕ → Set
  zero <NLogical zero = False
  zero <NLogical (succ n) = True
  (succ n) <NLogical zero = False
  (succ n) <NLogical (succ m) = n <NLogical m

infix 5 _<N_
record _<N_ (a : ℕ) (b : ℕ) : Set where
  constructor le
  field
    x : ℕ
    proof : (succ x) +N a ≡ b

infix 5 _<N'_
record _<N'_ (a : ℕ) (b : ℕ) : Set where
  constructor le'
  field
    x : ℕ
    .proof : (succ x) +N a ≡ b

infix 5 _≤N_
_≤N_ : ℕ → ℕ → Set
a ≤N b = (a <N b) || (a ≡ b)

succIsPositive : (a : ℕ) → zero <N succ a
succIsPositive a = le a (applyEquality succ (Semiring.commutative ℕSemiring a 0))

aLessSucc : (a : ℕ) → (a <NLogical succ a)
aLessSucc zero = record {}
aLessSucc (succ a) = aLessSucc a

private
  succPreservesInequalityLogical : {a b : ℕ} → (a <NLogical b) → (succ a <NLogical succ b)
  succPreservesInequalityLogical {a} {b} prAB = prAB

  lessTransitiveLogical : {a b c : ℕ} → (a <NLogical b) → (b <NLogical c) → (a <NLogical c)
  lessTransitiveLogical {a} {zero} {zero} prAB prBC = prAB
  lessTransitiveLogical {a} {(succ b)} {zero} prAB ()
  lessTransitiveLogical {zero} {zero} {(succ c)} prAB prBC = record {}
  lessTransitiveLogical {(succ a)} {zero} {(succ c)} () prBC
  lessTransitiveLogical {zero} {(succ b)} {(succ c)} prAB prBC = record {}
  lessTransitiveLogical {(succ a)} {(succ b)} {(succ c)} prAB prBC = lessTransitiveLogical {a} {b} {c} prAB prBC

  aLessXPlusSuccA : (a x : ℕ) → (a <NLogical x +N succ a)
  aLessXPlusSuccA a zero = aLessSucc a
  aLessXPlusSuccA zero (succ x) = record {}
  aLessXPlusSuccA (succ a) (succ x) = lessTransitiveLogical {a} {succ a} {x +N succ (succ a)} (aLessXPlusSuccA a zero) (aLessXPlusSuccA (succ a) x)

  leImpliesLogical<N : {a b : ℕ} → (a <N b) → (a <NLogical b)
  leImpliesLogical<N {zero} {zero} (le x ())
  leImpliesLogical<N {zero} {(succ b)} (le x proof) = record {}
  leImpliesLogical<N {(succ a)} {zero} (le x ())
  leImpliesLogical<N {(succ a)} {(succ .(succ a))} (le zero refl) = aLessSucc a
  leImpliesLogical<N {(succ a)} {(succ .(succ (x +N succ a)))} (le (succ x) refl) = succPreservesInequalityLogical {a} {succ (x +N succ a)} (lessTransitiveLogical {a} {succ a} {succ (x +N succ a)} (aLessSucc a) (aLessXPlusSuccA a x))

  logical<NImpliesLe : {a b : ℕ} → (a <NLogical b) → (a <N b)
  logical<NImpliesLe {zero} {zero} ()
  _<N_.x (logical<NImpliesLe {zero} {succ b} prAB) = b
  _<N_.proof (logical<NImpliesLe {zero} {succ b} prAB) = applyEquality succ (sumZeroRight b)
  logical<NImpliesLe {(succ a)} {zero} ()
  logical<NImpliesLe {(succ a)} {(succ b)} prAB with logical<NImpliesLe {a} prAB
  logical<NImpliesLe {(succ a)} {(succ .(succ (x +N a)))} prAB | le x refl = le x (applyEquality succ (transitivity (commutative x _) (applyEquality succ (commutative a _))))

lessTransitive : {a b c : ℕ} → (a <N b) → (b <N c) → (a <N c)
lessTransitive {a} {b} {c} prab prbc = logical<NImpliesLe (lessTransitiveLogical {a} {b} {c} (leImpliesLogical<N prab) (leImpliesLogical<N prbc))

lessIrreflexive : {a : ℕ} → (a <N a) → False
lessIrreflexive {zero} pr = leImpliesLogical<N pr
lessIrreflexive {succ a} pr = lessIrreflexive {a} (logical<NImpliesLe {a} {a} (leImpliesLogical<N {succ a} {succ a} pr))

succPreservesInequality : {a b : ℕ} → (a <N b) → (succ a <N succ b)
succPreservesInequality {a} {b} prAB = logical<NImpliesLe (succPreservesInequalityLogical {a} {b} (leImpliesLogical<N prAB))

canRemoveSuccFrom<N : {a b : ℕ} → (succ a <N succ b) → (a <N b)
canRemoveSuccFrom<N {a} {b} (le x proof) rewrite commutative x (succ a) | commutative a x = le x (succInjective proof)

a<SuccA : (a : ℕ) → a <N succ a
a<SuccA a = le zero refl

canAddToOneSideOfInequality : {a b : ℕ} (c : ℕ) → a <N b → a <N (b +N c)
canAddToOneSideOfInequality {a} {b} c (le x proof) = le (x +N c) (transitivity (applyEquality succ (equalityCommutative (+Associative x c a))) (transitivity (applyEquality (λ i → (succ x) +N i) (commutative c a)) (transitivity (applyEquality succ (+Associative x a c)) (applyEquality (_+N c) proof))))

addingIncreases : (a b : ℕ) → a <N a +N succ b
addingIncreases zero b = succIsPositive b
addingIncreases (succ a) b = succPreservesInequality (addingIncreases a b)

zeroNeverGreater : {a : ℕ} → (a <N zero) → False
zeroNeverGreater {a} (le x ())

noIntegersBetweenXAndSuccX : {a : ℕ} (x : ℕ) → (x <N a) → (a <N succ x) → False
noIntegersBetweenXAndSuccX {zero} x x<a a<sx = zeroNeverGreater x<a
noIntegersBetweenXAndSuccX {succ a} x (le y proof) (le z proof1) with succInjective proof1
... | ah rewrite (equalityCommutative proof) | (succExtracts z (y +N x)) | +Associative (succ z) y x | commutative (succ (z +N y)) x = lessIrreflexive {x} (le (z +N y) (transitivity (commutative _ x) ah))

<NWellDefined : {a b : ℕ} → (p1 : a <N b) → (p2 : a <N b) → _<N_.x p1 ≡ _<N_.x p2
<NWellDefined {a} {b} (le x proof) (le y proof1) = equalityCommutative r
  where
    q : y +N a ≡ x +N a
    q = succInjective {y +N a} {x +N a} (transitivity proof1 (equalityCommutative proof))
    r : y ≡ x
    r = canSubtractFromEqualityRight q

private
  orderIsTotal : (a b : ℕ) → ((a <N b) || (b <N a)) || (a ≡ b)
  orderIsTotal zero zero = inr refl
  orderIsTotal zero (succ b) = inl (inl (logical<NImpliesLe (record {})))
  orderIsTotal (succ a) zero = inl (inr (logical<NImpliesLe (record {})))
  orderIsTotal (succ a) (succ b) with orderIsTotal a b
  orderIsTotal (succ a) (succ b) | inl (inl x) = inl (inl (logical<NImpliesLe (leImpliesLogical<N x)))
  orderIsTotal (succ a) (succ b) | inl (inr x) = inl (inr (logical<NImpliesLe (leImpliesLogical<N x)))
  orderIsTotal (succ a) (succ b) | inr x = inr (applyEquality succ x)

  orderIsIrreflexive : {a b : ℕ} → (a <N b) → (b <N a) → False
  orderIsIrreflexive {zero} {b} prAB (le x ())
  orderIsIrreflexive {(succ a)} {zero} (le x ()) prBA
  orderIsIrreflexive {(succ a)} {(succ b)} prAB prBA = orderIsIrreflexive {a} {b} (logical<NImpliesLe (leImpliesLogical<N prAB)) (logical<NImpliesLe (leImpliesLogical<N prBA))

  orderIsTransitive : {a b c : ℕ} → (a <N b) → (b <N c) → (a <N c)
  orderIsTransitive {a} {.(succ (x +N a))} {.(succ (y +N succ (x +N a)))} (le x refl) (le y refl) = le (y +N succ x) (applyEquality succ (equalityCommutative (+Associative y (succ x) a)))

ℕTotalOrder : TotalOrder ℕ
PartialOrder._<_ (TotalOrder.order ℕTotalOrder) = _<N_
PartialOrder.irreflexive (TotalOrder.order ℕTotalOrder) = lessIrreflexive
PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) = orderIsTransitive
TotalOrder.totality ℕTotalOrder = orderIsTotal

cannotAddAndEnlarge : (a b : ℕ) → a <N succ (a +N b)
cannotAddAndEnlarge a b = le b (applyEquality succ (commutative b a))

cannotAddAndEnlarge' : {a b : ℕ} → a +N b <N a → False
cannotAddAndEnlarge' {a} {zero} pr rewrite sumZeroRight a = lessIrreflexive pr
cannotAddAndEnlarge' {a} {succ b} pr rewrite (succExtracts a b) = lessIrreflexive {a} (lessTransitive {a} {succ (a +N b)} {a} (cannotAddAndEnlarge a b) pr)

cannotAddAndEnlarge'' : {a b : ℕ} → a +N succ b ≡ a → False
cannotAddAndEnlarge'' {a} {b} pr = naughtE (equalityCommutative inter)
  where
    inter : succ b ≡ 0
    inter rewrite commutative a (succ b) = canSubtractFromEqualityRight pr

naturalsAreNonnegative : (a : ℕ) → (a <N zero) → False
naturalsAreNonnegative zero ()
naturalsAreNonnegative (succ x) ()

lessRespectsAddition : {a b : ℕ} (c : ℕ) → (a <N b) → ((a +N c) <N (b +N c))
lessRespectsAddition {a} {b} zero prAB rewrite commutative a 0 | commutative b 0 = prAB
lessRespectsAddition {a} {b} (succ c) prAB rewrite commutative a (succ c) | commutative b (succ c) | commutative c a | commutative c b = succPreservesInequality (lessRespectsAddition c prAB)

lessRespectsMultiplicationLeft : (a b c : ℕ) → (a <N b) → (zero <N c) → (c *N a <N c *N b)
lessRespectsMultiplicationLeft zero zero c (le x ()) cPos
lessRespectsMultiplicationLeft zero (succ b) zero prAB (le x ())
lessRespectsMultiplicationLeft zero (succ b) (succ c) prAB cPos = i
  where
    productNonzeroIsNonzero : {a b : ℕ} → zero <N a → zero <N b → zero <N a *N b
    productNonzeroIsNonzero {zero} {b} prA prB = prA
    productNonzeroIsNonzero {succ a} {zero} prA ()
    productNonzeroIsNonzero {succ a} {succ b} prA prB = le (b +N a *N succ b) (applyEquality succ (Semiring.sumZeroRight ℕSemiring _))

    j : zero <N succ c *N succ b
    j = productNonzeroIsNonzero cPos prAB
    i : succ c *N zero <N succ c *N succ b
    i = identityOfIndiscernablesLeft _<N_ j (equalityCommutative (productZeroRight c))
lessRespectsMultiplicationLeft (succ a) zero c (le x ()) cPos
lessRespectsMultiplicationLeft (succ a) (succ b) c prAB cPos = m
  where
    h : c *N a <N c *N b
    h = lessRespectsMultiplicationLeft a b c (canRemoveSuccFrom<N prAB) cPos
    j : c *N a +N c <N c *N b +N c
    j = lessRespectsAddition c h
    i : c *N succ a <N c *N b +N c
    i = identityOfIndiscernablesLeft _<N_ j (equalityCommutative (transitivity (multiplicationNIsCommutative c _) (transitivity (applyEquality (c +N_) (multiplicationNIsCommutative a _)) (commutative c _))))
    m : c *N succ a <N c *N succ b
    m = identityOfIndiscernablesRight _<N_ i (equalityCommutative (transitivity (multiplicationNIsCommutative c _) (transitivity (commutative c _) (applyEquality (_+N c) (multiplicationNIsCommutative b _)))))

canFlipMultiplicationsInIneq : {a b c d : ℕ} → (a *N b <N c *N d) → b *N a <N d *N c
canFlipMultiplicationsInIneq {a} {b} {c} {d} pr = identityOfIndiscernablesRight _<N_ (identityOfIndiscernablesLeft _<N_ pr (multiplicationNIsCommutative a b)) (multiplicationNIsCommutative c d)

lessRespectsMultiplication : (a b c : ℕ) → (a <N b) → (zero <N c) → (a *N c <N b *N c)
lessRespectsMultiplication a b c prAB cPos = canFlipMultiplicationsInIneq {c} {a} {c} {b} (lessRespectsMultiplicationLeft a b c prAB cPos)

<NTo<N' : {a b : ℕ} → a <N b → a <N' b
<NTo<N' (le x proof) = le' x proof

<N'To<N : {a b : ℕ} → a <N' b → a <N b
<N'To<N {a} {b} (le' x proof) = le x (squash proof)

<N'Refl : {a b : ℕ} → (p1 p2 : a <N' b) → p1 ≡ p2
<N'Refl p1 p2 with <NWellDefined (<N'To<N p1) (<N'To<N p2)
... | refl = refl
