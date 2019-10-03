{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Addition

module Numbers.Naturals.Order where

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

infix 5 _≤N_
_≤N_ : ℕ → ℕ → Set
a ≤N b = (a <N b) || (a ≡ b)

succIsPositive : (a : ℕ) → zero <N succ a
succIsPositive a = le a (applyEquality succ (additionNIsCommutative a 0))

aLessSucc : (a : ℕ) → (a <NLogical succ a)
aLessSucc zero = record {}
aLessSucc (succ a) = aLessSucc a

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
_<N_.proof (logical<NImpliesLe {zero} {succ b} prAB) = applyEquality succ (addZeroRight b)
logical<NImpliesLe {(succ a)} {zero} ()
logical<NImpliesLe {(succ a)} {(succ b)} prAB with logical<NImpliesLe {a} prAB
logical<NImpliesLe {(succ a)} {(succ .(succ (x +N a)))} prAB | le x refl = le x (succCanMove (succ x) a)

lessTransitive : {a b c : ℕ} → (a <N b) → (b <N c) → (a <N c)
lessTransitive {a} {b} {c} prab prbc = logical<NImpliesLe (lessTransitiveLogical {a} {b} {c} (leImpliesLogical<N prab) (leImpliesLogical<N prbc))

lessIrreflexive : {a : ℕ} → (a <N a) → False
lessIrreflexive {zero} pr = leImpliesLogical<N pr
lessIrreflexive {succ a} pr = lessIrreflexive {a} (logical<NImpliesLe {a} {a} (leImpliesLogical<N {succ a} {succ a} pr))

succPreservesInequality : {a b : ℕ} → (a <N b) → (succ a <N succ b)
succPreservesInequality {a} {b} prAB = logical<NImpliesLe (succPreservesInequalityLogical {a} {b} (leImpliesLogical<N prAB))

canRemoveSuccFrom<N : {a b : ℕ} → (succ a <N succ b) → (a <N b)
canRemoveSuccFrom<N {a} {b} (le x proof) rewrite additionNIsCommutative x (succ a) | additionNIsCommutative a x = le x (succInjective proof)

a<SuccA : (a : ℕ) → a <N succ a
a<SuccA a = le zero refl

canAddToOneSideOfInequality : {a b : ℕ} (c : ℕ) → a <N b → a <N (b +N c)
canAddToOneSideOfInequality {a} {b} c (le x proof) = le (x +N c) (transitivity (applyEquality succ (additionNIsAssociative x c a)) (transitivity (applyEquality (λ i → (succ x) +N i) (additionNIsCommutative c a)) (transitivity (applyEquality succ (equalityCommutative (additionNIsAssociative x a c))) (applyEquality (_+N c) proof))))

addingIncreases : (a b : ℕ) → a <N a +N succ b
addingIncreases zero b = succIsPositive b
addingIncreases (succ a) b = succPreservesInequality (addingIncreases a b)

zeroNeverGreater : {a : ℕ} → (a <N zero) → False
zeroNeverGreater {a} (le x ())

noIntegersBetweenXAndSuccX : {a : ℕ} (x : ℕ) → (x <N a) → (a <N succ x) → False
noIntegersBetweenXAndSuccX {zero} x x<a a<sx = zeroNeverGreater x<a
noIntegersBetweenXAndSuccX {succ a} x (le y proof) (le z proof1) with succInjective proof1
... | ah rewrite (equalityCommutative proof) | (succExtracts z (y +N x)) | equalityCommutative (additionNIsAssociative (succ z) y x) | additionNIsCommutative (succ (z +N y)) x = lessIrreflexive {x} (le (z +N y) (transitivity (additionNIsCommutative _ x) ah))

<NWellDefined : {a b : ℕ} → (p1 : a <N b) → (p2 : a <N b) → _<N_.x p1 ≡ _<N_.x p2
<NWellDefined {a} {b} (le x proof) (le y proof1) = equalityCommutative r
  where
    q : y +N a ≡ x +N a
    q = succInjective {y +N a} {x +N a} (transitivity proof1 (equalityCommutative proof))
    r : y ≡ x
    r = canSubtractFromEqualityRight q
