{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Numbers.BinaryNaturals.Definition
open import Numbers.BinaryNaturals.Addition
open import Numbers.BinaryNaturals.SubtractionGo
open import Numbers.BinaryNaturals.SubtractionGoPreservesCanonicalRight
open import Orders.Total.Definition
open import Semirings.Definition
open import Maybe

module Numbers.BinaryNaturals.Subtraction where

private
  aMinusAGo : (a : BinNat) → mapMaybe canonical (go zero a a) ≡ yes []
  aMinusAGo [] = refl
  aMinusAGo (zero :: a) with aMinusAGo a
  ... | bl with go zero a a
  aMinusAGo (zero :: a) | bl | yes x rewrite yesInjective bl = refl
  aMinusAGo (one :: a) with aMinusAGo a
  ... | bl with go zero a a
  aMinusAGo (one :: a) | bl | yes x rewrite yesInjective bl = refl

aMinusALemma : (a : BinNat) → mapMaybe canonical (mapMaybe (_::_ zero) (go zero a a)) ≡ yes []
aMinusALemma a with inspect (go zero a a)
aMinusALemma a | no with≡ x with aMinusAGo a
... | r rewrite x = exFalso (noNotYes r)
aMinusALemma a | yes xs with≡ pr with inspect (canonical xs)
aMinusALemma a | yes xs with≡ pr | [] with≡ pr2 rewrite pr | pr2 = refl
aMinusALemma a | yes xs with≡ pr | (x :: t) with≡ pr2 with aMinusAGo a
... | b rewrite pr | pr2 = exFalso (nonEmptyNotEmpty (yesInjective b))

aMinusA : (a : BinNat) → mapMaybe canonical (a -B a) ≡ yes []
aMinusA [] = refl
aMinusA (zero :: a) = aMinusALemma a
aMinusA (one :: a) = aMinusALemma a

goOne : (a b : BinNat) → mapMaybe canonical (go one (incr a) b) ≡ mapMaybe canonical (go zero a b)
goOne [] [] = refl
goOne [] (zero :: b) with inspect (go zero [] b)
goOne [] (zero :: b) | no with≡ pr rewrite pr = refl
goOne [] (zero :: b) | yes x with≡ pr with goZeroEmpty b pr
... | t with inspect (canonical x)
goOne [] (zero :: b) | yes x with≡ pr | t | [] with≡ pr2 rewrite pr | pr2 = refl
goOne [] (zero :: b) | yes x with≡ pr | t | (x₁ :: y) with≡ pr2 with goZeroEmpty' b pr
... | bl = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative pr2) bl))
goOne [] (one :: b) with inspect (go one [] b)
goOne [] (one :: b) | no with≡ pr rewrite pr = refl
goOne [] (one :: b) | yes x with≡ pr = exFalso (goOneEmpty b pr)
goOne (zero :: a) [] = refl
goOne (zero :: a) (zero :: b) = refl
goOne (zero :: a) (one :: b) = refl
goOne (one :: a) [] with inspect (go one (incr a) [])
goOne (one :: a) [] | no with≡ pr with goOne a []
... | bl rewrite pr | goEmpty a = exFalso (noNotYes bl)
goOne (one :: a) [] | yes y with≡ pr with goOne a []
... | bl rewrite pr = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity bl (applyEquality (mapMaybe canonical) (goEmpty a))))
goOne (one :: a) (zero :: b) with inspect (go zero a b)
goOne (one :: a) (zero :: b) | no with≡ pr with inspect (go one (incr a) b)
goOne (one :: a) (zero :: b) | no with≡ pr | no with≡ x rewrite pr | x = refl
goOne (one :: a) (zero :: b) | no with≡ pr | yes y with≡ x with goOne a b
... | f rewrite pr | x = exFalso (noNotYes (equalityCommutative f))
goOne (one :: a) (zero :: b) | yes y with≡ pr with inspect (go one (incr a) b)
goOne (one :: a) (zero :: b) | yes y with≡ pr | no with≡ x with goOne a b
... | f rewrite pr | x = exFalso (noNotYes f)
goOne (one :: a) (zero :: b) | yes y with≡ pr | yes z with≡ x rewrite pr | x = applyEquality (λ i → yes (one :: i)) (yesInjective (transitivity (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative x)) (goOne a b)) (applyEquality (mapMaybe canonical) pr)))
goOne (one :: a) (one :: b) with inspect (go zero a b)
goOne (one :: a) (one :: b) | no with≡ pr with inspect (go one (incr a) b)
goOne (one :: a) (one :: b) | no with≡ pr | no with≡ pr2 rewrite pr | pr2 = refl
goOne (one :: a) (one :: b) | no with≡ pr | yes x with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr)) (transitivity (equalityCommutative (goOne a b)) (applyEquality (mapMaybe canonical) pr2))))
goOne (one :: a) (one :: b) | yes y with≡ pr with inspect (go one (incr a) b)
goOne (one :: a) (one :: b) | yes y with≡ pr | yes z with≡ pr2 rewrite pr | pr2 = applyEquality yes t
  where
    u : canonical z ≡ canonical y
    u = yesInjective (transitivity (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (goOne a b)) (applyEquality (mapMaybe canonical) pr))
    t : canonical (zero :: z) ≡ canonical (zero :: y)
    t with inspect (canonical z)
    t | [] with≡ pr1 rewrite equalityCommutative u | pr1 = refl
    t | (x :: bl) with≡ pr rewrite equalityCommutative u | pr = refl
goOne (one :: a) (one :: b) | yes y with≡ pr | no with≡ pr2 rewrite pr | pr2 = exFalso (noNotYes (transitivity (equalityCommutative (applyEquality (mapMaybe canonical) pr2)) (transitivity (goOne a b) (applyEquality (mapMaybe canonical) pr))))

plusThenMinus : (a b : BinNat) → mapMaybe canonical ((a +B b) -B b) ≡ yes (canonical a)
plusThenMinus [] b = aMinusA b
plusThenMinus (zero :: a) [] = refl
plusThenMinus (zero :: a) (zero :: b) = t
  where
    t : mapMaybe canonical (mapMaybe (zero ::_) (go zero (a +B b) b)) ≡ yes (canonical (zero :: a))
    t with inspect (go zero (a +B b) b)
    t | no with≡ x with plusThenMinus a b
    ... | bl rewrite x = exFalso (noNotYes bl)
    t | yes y with≡ x with plusThenMinus a b
    ... | f rewrite x = applyEquality yes u
      where
        u : canonical (zero :: y) ≡ canonical (zero :: a)
        u with inspect (canonical y)
        u | [] with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
        u | (x :: bl) with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
plusThenMinus (zero :: a) (one :: b) = t
  where
    t : mapMaybe canonical (mapMaybe (zero ::_) (go zero (a +B b) b)) ≡ yes (canonical (zero :: a))
    t with inspect (go zero (a +B b) b)
    t | no with≡ x with plusThenMinus a b
    ... | bl rewrite x = exFalso (noNotYes bl)
    t | yes y with≡ x with plusThenMinus a b
    ... | f rewrite x = applyEquality yes u
      where
        u : canonical (zero :: y) ≡ canonical (zero :: a)
        u with inspect (canonical y)
        u | [] with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
        u | (x :: bl) with≡ pr rewrite pr | equalityCommutative (yesInjective f) = refl
plusThenMinus (one :: a) [] = refl
plusThenMinus (one :: a) (zero :: b) = t
  where
    t : mapMaybe canonical (mapMaybe (_::_ one) (go zero (a +B b) b)) ≡ yes (one :: canonical a)
    t with inspect (go zero (a +B b) b)
    t | no with≡ x with plusThenMinus a b
    ... | bl rewrite x = exFalso (noNotYes bl)
    t | yes y with≡ x with plusThenMinus a b
    ... | bl rewrite x = applyEquality (λ i → yes (one :: i)) (yesInjective bl)
plusThenMinus (one :: a) (one :: b) = t
  where
    t : mapMaybe canonical (mapMaybe (_::_ one) (go one (incr (a +B b)) b)) ≡ yes (one :: canonical a)
    t with inspect (go one (incr (a +B b)) b)
    t | no with≡ x with goOne (a +B b) b
    ... | f rewrite x | plusThenMinus a b = exFalso (noNotYes f)
    t | yes y with≡ x with goOne (a +B b) b
    ... | f rewrite x | plusThenMinus a b = applyEquality (λ i → yes (one :: i)) (yesInjective f)

subLemma : (a b : ℕ) → a <N b → succ (a +N a) <N b +N b
subLemma a b a<b with TotalOrder.totality ℕTotalOrder (succ (a +N a)) (b +N b)
subLemma a b a<b | inl (inl x) = x
subLemma a b a<b | inl (inr x) = exFalso (noIntegersBetweenXAndSuccX (a +N a) (addStrongInequalities a<b a<b) x)
subLemma a b a<b | inr x = exFalso (parity a b (transitivity (applyEquality (succ a +N_) (Semiring.sumZeroRight ℕSemiring a)) (transitivity x (applyEquality (b +N_) (equalityCommutative (Semiring.sumZeroRight ℕSemiring b))))))

subLemma2 : (a b : ℕ) → a <N b → 2 *N a <N succ (2 *N b)
subLemma2 a b a<b with TotalOrder.totality ℕTotalOrder (2 *N a) (succ (2 *N b))
subLemma2 a b a<b | inl (inl x) = x
subLemma2 a b a<b | inl (inr x) = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder x (TotalOrder.<Transitive ℕTotalOrder (lessRespectsMultiplicationLeft a b 2 a<b (le 1 refl)) (le 0 refl))))
subLemma2 a b a<b | inr x = exFalso (parity b a (equalityCommutative x))

subtraction : (a b : BinNat) → a -B b ≡ no → binNatToN a <N binNatToN b
subtraction' : (a b : BinNat) → go one a b ≡ no → (binNatToN a <N binNatToN b) || (binNatToN a ≡ binNatToN b)

subtraction' [] [] pr = inr refl
subtraction' [] (x :: b) pr with TotalOrder.totality ℕTotalOrder 0 (binNatToN (x :: b))
subtraction' [] (x :: b) pr | inl (inl x₁) = inl x₁
subtraction' [] (x :: b) pr | inr x₁ = inr x₁
subtraction' (zero :: a) [] pr with subtraction' a [] (mapMaybePreservesNo pr)
subtraction' (zero :: a) [] pr | inr x rewrite x = inr refl
subtraction' (zero :: a) (zero :: b) pr with subtraction' a b (mapMaybePreservesNo pr)
subtraction' (zero :: a) (zero :: b) pr | inl x = inl (lessRespectsMultiplicationLeft (binNatToN a) (binNatToN b) 2 x (le 1 refl))
subtraction' (zero :: a) (zero :: b) pr | inr x rewrite x = inr refl
subtraction' (zero :: a) (one :: b) pr with subtraction' a b (mapMaybePreservesNo pr)
subtraction' (zero :: a) (one :: b) pr | inl x = inl (subLemma2 (binNatToN a) (binNatToN b) x)
subtraction' (zero :: a) (one :: b) pr | inr x rewrite x = inl (le zero refl)
subtraction' (one :: a) (zero :: b) pr with subtraction a b (mapMaybePreservesNo pr)
... | t rewrite Semiring.sumZeroRight ℕSemiring (binNatToN a) | Semiring.sumZeroRight ℕSemiring (binNatToN b) = inl (subLemma (binNatToN a) (binNatToN b) t)
subtraction' (one :: a) (one :: b) pr with subtraction' a b (mapMaybePreservesNo pr)
subtraction' (one :: a) (one :: b) pr | inl x = inl (succPreservesInequality (lessRespectsMultiplicationLeft (binNatToN a) (binNatToN b) 2 x (le 1 refl)))
subtraction' (one :: a) (one :: b) pr | inr x rewrite x = inr refl

subtraction [] (zero :: b) pr with inspect (binNatToN b)
subtraction [] (zero :: b) pr | zero with≡ pr1 = exFalso (noNotYes (transitivity (applyEquality (mapMaybe canonical) (equalityCommutative pr)) (transitivity (goPreservesCanonicalRight zero [] b) (transitivity (applyEquality (λ i → mapMaybe canonical (go zero [] i)) (binNatToNZero b pr1)) refl))))
subtraction [] (zero :: b) pr | (succ bl) with≡ pr1 rewrite pr | pr1 = succIsPositive _
subtraction [] (one :: b) pr = succIsPositive _
subtraction (zero :: a) (zero :: b) pr = lessRespectsMultiplicationLeft (binNatToN a) (binNatToN b) 2 u (le 1 refl)
  where
    u : binNatToN a <N binNatToN b
    u = subtraction a b (mapMaybePreservesNo pr)
subtraction (zero :: a) (one :: b) pr with subtraction' a b (mapMaybePreservesNo pr)
subtraction (zero :: a) (one :: b) pr | inl x = subLemma2 (binNatToN a) (binNatToN b) x
subtraction (zero :: a) (one :: b) pr | inr x rewrite x = le zero refl
subtraction (one :: a) (zero :: b) pr rewrite Semiring.sumZeroRight ℕSemiring (binNatToN a) | Semiring.sumZeroRight ℕSemiring (binNatToN b) = subLemma (binNatToN a) (binNatToN b) u
  where
    u : binNatToN a <N binNatToN b
    u = subtraction a b (mapMaybePreservesNo pr)
subtraction (one :: a) (one :: b) pr = succPreservesInequality (lessRespectsMultiplicationLeft (binNatToN a) (binNatToN b) 2 u (le 1 refl))
  where
    u : binNatToN a <N binNatToN b
    u = subtraction a b (mapMaybePreservesNo pr)

subLemma4 : (a b : BinNat) {t : BinNat} → go one a b ≡ no → go zero a b ≡ yes t → canonical t ≡ []
subLemma4 [] [] {t} pr1 pr2 rewrite yesInjective (equalityCommutative pr2) = refl
subLemma4 [] (x :: b) {t} pr1 pr2 = goZeroEmpty' (x :: b) pr2
subLemma4 (zero :: a) [] {t} pr1 pr2 with inspect (go one a [])
subLemma4 (zero :: a) [] {t} pr1 pr2 | no with≡ pr3 with subLemma4 a [] pr3 (goEmpty a)
... | bl with applyEquality canonical (yesInjective pr2)
... | th rewrite bl = equalityCommutative th
subLemma4 (zero :: a) [] {t} pr1 pr2 | yes x with≡ pr3 rewrite pr3 = exFalso (noNotYes (equalityCommutative pr1))
subLemma4 (zero :: a) (zero :: b) {t} pr1 pr2 with inspect (go one a b)
subLemma4 (zero :: a) (zero :: b) {t} pr1 pr2 | no with≡ pr3 with inspect (go zero a b)
subLemma4 (zero :: a) (zero :: b) {t} pr1 pr2 | no with≡ pr3 | no with≡ pr4 rewrite pr4 = exFalso (noNotYes pr2)
subLemma4 (zero :: a) (zero :: b) {t} pr1 pr2 | no with≡ pr3 | yes x with≡ pr4 with subLemma4 a b pr3 pr4
... | bl rewrite pr3 | pr4 = ans
  where
    ans : canonical t ≡ []
    ans rewrite equalityCommutative (applyEquality canonical (yesInjective pr2)) | bl = refl
subLemma4 (zero :: a) (zero :: b) {t} pr1 pr2 | yes x with≡ pr3 rewrite pr3 = exFalso (noNotYes (equalityCommutative pr1))
subLemma4 (zero :: a) (one :: b) {t} pr1 pr2 with go one a b
... | no = exFalso (noNotYes pr2)
subLemma4 (zero :: a) (one :: b) {t} pr1 pr2 | yes x = exFalso (noNotYes (equalityCommutative pr1))
subLemma4 (one :: a) (zero :: b) {t} pr1 pr2 with go zero a b
subLemma4 (one :: a) (zero :: b) {t} pr1 pr2 | no = exFalso (noNotYes pr2)
subLemma4 (one :: a) (zero :: b) {t} pr1 pr2 | yes x = exFalso (noNotYes (equalityCommutative pr1))
subLemma4 (one :: a) (one :: b) {t} pr1 pr2 with inspect (go zero a b)
subLemma4 (one :: a) (one :: b) {t} pr1 pr2 | no with≡ pr3 rewrite pr3 = exFalso (noNotYes pr2)
subLemma4 (one :: a) (one :: b) {t} pr1 pr2 | yes x with≡ pr3 with inspect (go one a b)
subLemma4 (one :: a) (one :: b) {t} pr1 pr2 | yes x with≡ pr3 | no with≡ pr4 with subLemma4 a b pr4 pr3
... | bl rewrite pr3 | pr4 | bl = ans
  where
    ans : canonical t ≡ []
    ans rewrite equalityCommutative (applyEquality canonical (yesInjective pr2)) | bl = refl
subLemma4 (one :: a) (one :: b) {t} pr1 pr2 | yes x with≡ pr3 | yes x₁ with≡ pr4 rewrite pr4 = exFalso (noNotYes (equalityCommutative pr1))

goOneFromZero : (a b : BinNat) → go zero a b ≡ no → go one a b ≡ no
goOneFromZero [] (zero :: b) pr = refl
goOneFromZero [] (one :: b) pr = refl
goOneFromZero (zero :: a) (zero :: b) pr rewrite goOneFromZero a b (mapMaybePreservesNo pr) = refl
goOneFromZero (zero :: a) (one :: b) pr rewrite (mapMaybePreservesNo pr) = refl
goOneFromZero (one :: a) (zero :: b) pr rewrite (mapMaybePreservesNo pr) = refl
goOneFromZero (one :: a) (one :: b) pr rewrite goOneFromZero a b (mapMaybePreservesNo pr) = refl

subLemma5 : (a b : BinNat) → mapMaybe canonical (go zero a b) ≡ yes [] → go one a b ≡ no
subLemma5 [] b pr = goOneEmpty' b
subLemma5 (zero :: a) [] pr with inspect (canonical a)
subLemma5 (zero :: a) [] pr | (z :: zs) with≡ pr2 rewrite pr2 = exFalso (nonEmptyNotEmpty (yesInjective pr))
subLemma5 (zero :: a) [] pr | [] with≡ pr2 rewrite pr2 = applyEquality (mapMaybe (one ::_)) (subLemma5 a [] (transitivity (applyEquality (mapMaybe canonical) (goEmpty a)) (applyEquality yes pr2)))
subLemma5 (zero :: a) (zero :: b) pr with inspect (go zero a b)
subLemma5 (zero :: a) (zero :: b) pr | no with≡ pr2 rewrite pr2 = exFalso (noNotYes pr)
subLemma5 (zero :: a) (zero :: b) pr | yes x with≡ pr2 with inspect (canonical x)
subLemma5 (zero :: a) (zero :: b) pr | yes x with≡ pr2 | [] with≡ pr3 rewrite pr | pr2 | pr3 = applyEquality (mapMaybe (one ::_)) (subLemma5 a b (transitivity (applyEquality (mapMaybe canonical) pr2) (applyEquality yes pr3)))
subLemma5 (zero :: a) (zero :: b) pr | yes x with≡ pr2 | (x₁ :: bl) with≡ pr3 rewrite pr | pr2 | pr3 = exFalso (nonEmptyNotEmpty (yesInjective pr))
subLemma5 (zero :: a) (one :: b) pr with (go one a b)
subLemma5 (zero :: a) (one :: b) pr | no = exFalso (noNotYes pr)
subLemma5 (zero :: a) (one :: b) pr | yes y = exFalso (nonEmptyNotEmpty (yesInjective pr))
subLemma5 (one :: a) (zero :: b) pr with go zero a b
subLemma5 (one :: a) (zero :: b) pr | no = exFalso (noNotYes pr)
subLemma5 (one :: a) (zero :: b) pr | yes x = exFalso (nonEmptyNotEmpty (yesInjective pr))
subLemma5 (one :: a) (one :: b) pr with inspect (go zero a b)
subLemma5 (one :: a) (one :: b) pr | yes x with≡ pr2 with inspect (canonical x)
subLemma5 (one :: a) (one :: b) pr | yes x with≡ pr2 | [] with≡ pr3 rewrite pr | pr2 | pr3 = applyEquality (mapMaybe (one ::_)) (subLemma5 a b (transitivity (applyEquality (mapMaybe canonical) pr2) (applyEquality yes pr3)))
subLemma5 (one :: a) (one :: b) pr | yes x with≡ pr2 | (x₁ :: y) with≡ pr3 rewrite pr | pr2 | pr3 = exFalso (nonEmptyNotEmpty (yesInjective pr))
subLemma5 (one :: a) (one :: b) pr | no with≡ pr2 rewrite pr2 = exFalso (noNotYes pr)

subLemma3 : (a b : BinNat) → go zero a b ≡ no → (go zero (incr a) b ≡ no) || (mapMaybe canonical (go zero (incr a) b) ≡ yes [])
subLemma3 a b pr with inspect (go zero (incr a) b)
subLemma3 a b pr | no with≡ x = inl x
subLemma3 [] (zero :: b) pr | yes y with≡ pr1 rewrite pr = exFalso (noNotYes pr1)
subLemma3 [] (one :: b) pr | yes y with≡ pr1 with inspect (go zero [] b)
subLemma3 [] (one :: b) pr | yes y with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes pr1)
subLemma3 [] (one :: b) pr | yes y with≡ pr1 | yes x with≡ pr2 with goZeroEmpty' b pr2
... | f rewrite pr1 | pr2 | equalityCommutative (yesInjective pr1) | f = inr refl
subLemma3 (zero :: a) (zero :: b) pr | yes y with≡ pr1 rewrite mapMaybePreservesNo pr = exFalso (noNotYes pr1)
subLemma3 (zero :: a) (one :: b) pr | yes y with≡ pr1 with inspect (go zero a b)
subLemma3 (zero :: a) (one :: b) pr | yes y with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes pr1)
subLemma3 (zero :: a) (one :: b) pr | yes y with≡ pr1 | yes x with≡ pr2 with inspect (canonical x)
... | [] with≡ pr3 rewrite pr1 | pr2 | equalityCommutative (yesInjective pr1) | pr3 = inr refl
... | (z :: zs) with≡ pr3 with inspect (go one a b)
subLemma3 (zero :: a) (one :: b) pr | yes y with≡ pr1 | yes x with≡ pr2 | (z :: zs) with≡ pr3 | no with≡ pr4 rewrite pr1 | pr2 | pr3 | pr4 = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative pr3) (subLemma4 a b pr4 pr2)))
subLemma3 (zero :: a) (one :: b) pr | yes y with≡ pr1 | yes x with≡ pr2 | (z :: zs) with≡ pr3 | yes x₁ with≡ pr4 rewrite pr1 | pr2 | pr3 | pr4 = exFalso (noNotYes (equalityCommutative pr))
subLemma3 (one :: a) (zero :: b) pr | yes y with≡ pr1 with subLemma3 a b (mapMaybePreservesNo pr)
subLemma3 (one :: a) (zero :: b) pr | yes y with≡ pr1 | inl x rewrite x = inl refl
subLemma3 (one :: a) (zero :: b) pr | yes y with≡ pr1 | inr x with inspect (go zero (incr a) b)
... | no with≡ pr2 rewrite pr1 | pr2 = exFalso (noNotYes x)
... | yes z with≡ pr2 rewrite pr1 | pr2 = inr (applyEquality yes (transitivity (transitivity (applyEquality canonical (yesInjective (equalityCommutative pr1))) r) (yesInjective x)))
  where
    r : canonical (zero :: z) ≡ canonical z
    r rewrite yesInjective x = refl
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 with subLemma3 a b (mapMaybePreservesNo pr)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inl x with inspect (go one (incr a) b)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inl th | no with≡ pr2 rewrite pr2 = exFalso (noNotYes pr1)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inl th | yes x with≡ pr2 with goOneFromZero (incr a) b th
... | bad rewrite pr2 = exFalso (noNotYes (equalityCommutative bad))
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inr x with inspect (go one (incr a) b)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inr x | no with≡ pr2 rewrite pr2 = exFalso (noNotYes pr1)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inr th | yes z with≡ pr2 with inspect (go zero (incr a) b)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inr th | yes z with≡ pr2 | no with≡ pr3 rewrite pr3 = exFalso (noNotYes th)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inr th | yes z with≡ pr2 | yes x with≡ pr3 with inspect (go zero a b)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inr th | yes z with≡ pr2 | yes x with≡ pr3 | no with≡ pr4 rewrite pr1 | th | pr2 | pr3 | pr4 | equalityCommutative (yesInjective pr1) = exFalso false
  where
    false : False
    false with applyEquality (mapMaybe canonical) pr3
    ... | f rewrite th | subLemma5 (incr a) b f = exFalso (noNotYes pr2)
subLemma3 (one :: a) (one :: b) pr | yes y with≡ pr1 | inr th | yes z with≡ pr2 | yes x with≡ pr3 | yes w with≡ pr4 rewrite pr4 = exFalso (noNotYes (equalityCommutative pr))

goIncrOne : (a b : BinNat) → mapMaybe canonical (go one a b) ≡ mapMaybe canonical (go zero a (incr b))
goIncrOne [] b rewrite goOneEmpty' b | goZeroIncr b = refl
goIncrOne (zero :: a) [] = refl
goIncrOne (zero :: a) (zero :: b) = refl
goIncrOne (zero :: a) (one :: b) with inspect (go one a b)
goIncrOne (zero :: a) (one :: b) | no with≡ pr1 with inspect (go zero a (incr b))
goIncrOne (zero :: a) (one :: b) | no with≡ pr1 | no with≡ pr2 rewrite pr1 | pr2 = refl
goIncrOne (zero :: a) (one :: b) | no with≡ pr1 | yes x with≡ pr2 with goIncrOne a b
... | f rewrite pr1 | pr2 = exFalso (noNotYes f)
goIncrOne (zero :: a) (one :: b) | yes x with≡ pr1 with inspect (go zero a (incr b))
goIncrOne (zero :: a) (one :: b) | yes x with≡ pr1 | no with≡ pr2 with goIncrOne a b
... | f rewrite pr1 | pr2 = exFalso (noNotYes (equalityCommutative f))
goIncrOne (zero :: a) (one :: b) | yes x with≡ pr1 | yes y with≡ pr2 with goIncrOne a b
... | f rewrite pr1 | pr2 | yesInjective f = refl
goIncrOne (one :: a) [] rewrite goEmpty a = refl
goIncrOne (one :: a) (zero :: b) = refl
goIncrOne (one :: a) (one :: b) with inspect (go one a b)
goIncrOne (one :: a) (one :: b) | no with≡ pr with inspect (go zero a (incr b))
goIncrOne (one :: a) (one :: b) | no with≡ pr | no with≡ pr2 with goIncrOne a b
... | f rewrite pr | pr2 = refl
goIncrOne (one :: a) (one :: b) | no with≡ pr | yes x with≡ pr2 with goIncrOne a b
... | f rewrite pr | pr2 = exFalso (noNotYes f)
goIncrOne (one :: a) (one :: b) | yes x with≡ pr with inspect (go zero a (incr b))
goIncrOne (one :: a) (one :: b) | yes x with≡ pr | no with≡ pr2 with goIncrOne a b
... | f rewrite pr | pr2 = exFalso (noNotYes (equalityCommutative f))
goIncrOne (one :: a) (one :: b) | yes x with≡ pr | yes y with≡ pr2 with goIncrOne a b
... | f rewrite pr | pr2 | yesInjective f = refl

goIncrIncr : (a b : BinNat) → mapMaybe canonical (go zero (incr a) (incr b)) ≡ mapMaybe canonical (go zero a b)
goIncrIncr [] [] = refl
goIncrIncr [] (zero :: b) with inspect (go zero [] b)
... | no with≡ pr rewrite goIncrIncr [] b | pr = refl
... | yes y with≡ pr rewrite goIncrIncr [] b | pr | goZeroEmpty' b {y} pr = refl
goIncrIncr [] (one :: b) rewrite goZeroIncr b = refl
goIncrIncr (zero :: a) [] rewrite goEmpty a = refl
goIncrIncr (zero :: a) (zero :: b) = refl
goIncrIncr (zero :: a) (one :: b) with inspect (go zero a (incr b))
goIncrIncr (zero :: a) (one :: b) | no with≡ pr with inspect (go one a b)
goIncrIncr (zero :: a) (one :: b) | no with≡ pr | no with≡ pr2 rewrite pr | pr2 = refl
goIncrIncr (zero :: a) (one :: b) | no with≡ pr | yes x with≡ pr2 with goIncrOne a b
... | f rewrite pr | pr2 = exFalso (noNotYes (equalityCommutative f))
goIncrIncr (zero :: a) (one :: b) | yes y with≡ pr with inspect (go one a b)
goIncrIncr (zero :: a) (one :: b) | yes y with≡ pr | yes z with≡ pr2 with goIncrOne a b
... | f rewrite pr | pr2 = applyEquality (λ i → yes (one :: i)) (equalityCommutative (yesInjective f))
goIncrIncr (zero :: a) (one :: b) | yes y with≡ pr | no with≡ pr2 with goIncrOne a b
... | f rewrite pr | pr2 = exFalso (noNotYes f)
goIncrIncr (one :: a) [] with goOne a []
... | f with go one (incr a) []
goIncrIncr (one :: a) [] | f | no rewrite goEmpty a = exFalso (noNotYes f)
goIncrIncr (one :: a) [] | f | yes x rewrite goEmpty a | yesInjective f = refl
goIncrIncr (one :: a) (zero :: b) with goOne a b
... | f with go one (incr a) b
goIncrIncr (one :: a) (zero :: b) | f | no with go zero a b
goIncrIncr (one :: a) (zero :: b) | f | no | no = refl
goIncrIncr (one :: a) (zero :: b) | f | yes x with go zero a b
goIncrIncr (one :: a) (zero :: b) | f | yes x | yes x₁ rewrite yesInjective f = refl
goIncrIncr (one :: a) (one :: b) with goIncrIncr a b
... | f with go zero a b
goIncrIncr (one :: a) (one :: b) | f | no with go zero (incr a) (incr b)
goIncrIncr (one :: a) (one :: b) | f | no | no = refl
goIncrIncr (one :: a) (one :: b) | f | yes x with go zero (incr a) (incr b)
goIncrIncr (one :: a) (one :: b) | f | yes x | yes x₁ rewrite yesInjective f = refl

subtractionConverse : (a b : ℕ) → a <N b → go zero (NToBinNat a) (NToBinNat b) ≡ no
subtractionConverse zero (succ b) a<b with NToBinNat b
subtractionConverse zero (succ b) a<b | [] = refl
subtractionConverse zero (succ b) a<b | zero :: bl = refl
subtractionConverse zero (succ b) a<b | one :: bl = goZeroIncr bl
subtractionConverse (succ a) (succ b) a<b with inspect (NToBinNat a)
subtractionConverse (succ a) (succ b) a<b | [] with≡ pr with inspect (NToBinNat b)
subtractionConverse (succ a) (succ b) a<b | [] with≡ pr | [] with≡ pr2 rewrite NToBinNatZero a pr | NToBinNatZero b pr2 = exFalso (TotalOrder.irreflexive ℕTotalOrder a<b)
subtractionConverse (succ a) (succ zero) a<b | [] with≡ pr | (zero :: y) with≡ pr2 rewrite NToBinNatZero a pr | pr2 = exFalso (TotalOrder.irreflexive ℕTotalOrder a<b)
subtractionConverse (succ a) (succ (succ b)) a<b | [] with≡ pr | (zero :: y) with≡ pr2 with inspect (go zero [] y)
... | no with≡ pr3 rewrite NToBinNatZero a pr | pr2 | pr3 = refl
... | yes t with≡ pr3 with applyEquality canonical pr2
... | g rewrite (goZeroEmpty y pr3) = exFalso (incrNonzero (NToBinNat b) g)
subtractionConverse (succ a) (succ b) a<b | [] with≡ pr | (one :: y) with≡ pr2 rewrite NToBinNatZero a pr | pr2 = applyEquality (mapMaybe (one ::_)) (goZeroIncr y)
subtractionConverse (succ a) (succ b) a<b | (zero :: y) with≡ pr with inspect (NToBinNat b)
subtractionConverse (succ a) (succ b) a<b | (zero :: y) with≡ pr | [] with≡ pr2 rewrite NToBinNatZero b pr2 = exFalso (bad a<b)
  where
    bad : {a : ℕ} → succ a <N 1 → False
    bad {zero} (le zero ())
    bad {zero} (le (succ x) ())
    bad {succ a} (le zero ())
    bad {succ a} (le (succ x) ())
subtractionConverse (succ a) (succ b) a<b | (zero :: y) with≡ pr | (zero :: z) with≡ pr2 rewrite pr | pr2 = applyEquality (mapMaybe (zero ::_)) (mapMaybePreservesNo u)
  where
    t : go zero (NToBinNat a) (NToBinNat b) ≡ no
    t = subtractionConverse a b (canRemoveSuccFrom<N a<b)
    u : go zero (zero :: y) (zero :: z) ≡ no
    u = transitivity (transitivity {x = _} {go zero (NToBinNat a) (zero :: z)} (applyEquality (λ i → go zero i (zero :: z)) (equalityCommutative pr)) (applyEquality (go zero (NToBinNat a)) (equalityCommutative pr2))) t
subtractionConverse (succ a) (succ b) a<b | (zero :: y) with≡ pr | (one :: z) with≡ pr2 with subtractionConverse a (succ b) (le (succ (_<N_.x a<b)) (transitivity (applyEquality succ (transitivity (applyEquality succ (Semiring.commutative ℕSemiring (_<N_.x a<b) a)) (Semiring.commutative ℕSemiring (succ a) (_<N_.x a<b)))) (_<N_.proof a<b)))
subtractionConverse (succ a) (succ b) a<b | (zero :: y) with≡ pr | (one :: z) with≡ pr2 | thing=no with subLemma3 (NToBinNat a) (incr (NToBinNat b)) thing=no
subtractionConverse (succ a) (succ b) a<b | (zero :: y) with≡ pr | (one :: z) with≡ pr2 | thing=no | inl x = x
subtractionConverse (succ a) (succ b) a<b | (zero :: y) with≡ pr | (one :: z) with≡ pr2 | thing=no | inr x rewrite pr | pr2 | mapMaybePreservesNo thing=no = exFalso (noNotYes x)
subtractionConverse (succ a) (succ b) a<b | (one :: y) with≡ pr with goIncrIncr (NToBinNat a) (NToBinNat b)
... | f rewrite subtractionConverse a b (canRemoveSuccFrom<N a<b) = mapMaybePreservesNo f

bad : (b : ℕ) {t : BinNat} → incr (NToBinNat b) ≡ zero :: t → canonical t ≡ [] → False
bad b {c} t pr with applyEquality canonical t
... | bl with canonical c
bad b {c} t pr | bl | [] = exFalso (incrNonzero (NToBinNat b) bl)

lemma6 : (a : BinNat) (b : ℕ) → canonical a ≡ [] → NToBinNat b ≡ one :: a → a ≡ []
lemma6 [] b pr1 pr2 = refl
lemma6 (a :: as) b pr1 pr2 with applyEquality canonical pr2
lemma6 (a :: as) b pr1 pr2 | th rewrite pr1 | equalityCommutative (NToBinNatIsCanonical b) | pr2 = exFalso (bad' th)
  where
    bad' : one :: a :: as ≡ one :: [] → False
    bad' ()

doublingLemma : (y : BinNat) → NToBinNat (2 *N binNatToN y) ≡ canonical (zero :: y)
doublingLemma y with inspect (canonical y)
doublingLemma y | [] with≡ pr rewrite binNatToNZero' y pr | pr = refl
doublingLemma y | (a :: as) with≡ pr with inspect (binNatToN y)
doublingLemma y | (a :: as) with≡ pr | zero with≡ pr2 rewrite binNatToNZero y pr2 = exFalso (nonEmptyNotEmpty (equalityCommutative pr))
doublingLemma y | (a :: as) with≡ pr | succ bl with≡ pr2 rewrite pr | pr2 | doubleIsBitShift' bl | equalityCommutative pr = applyEquality (zero ::_) (equalityCommutative (transitivity (equalityCommutative (binToBin y)) (applyEquality NToBinNat pr2)))

private
  doubling : (a : ℕ) {y : BinNat} → (NToBinNat a ≡ zero :: y) → binNatToN y +N (binNatToN y +N 0) ≡ a
  doubling a {y} pr = NToBinNatInj (binNatToN y +N (binNatToN y +N zero)) a (transitivity (transitivity (equalityCommutative (NToBinNatIsCanonical (binNatToN y +N (binNatToN y +N zero)))) (doublingLemma y)) (applyEquality canonical (equalityCommutative pr)))

subtraction2 : (a b : ℕ) {t : BinNat} → (NToBinNat a) -B (NToBinNat b) ≡ yes t → (binNatToN t) +N b ≡ a
subtraction2 zero zero {t} pr rewrite yesInjective (equalityCommutative pr) = refl
subtraction2 zero (succ b) pr with goZeroEmpty (NToBinNat (succ b)) pr
... | t = exFalso (incrNonzero (NToBinNat b) t)
subtraction2 (succ a) b {t} pr with inspect (NToBinNat a)
subtraction2 (succ a) b {t} pr | [] with≡ pr2 with inspect (NToBinNat b)
subtraction2 (succ a) b {t} pr | [] with≡ pr2 | [] with≡ pr3 rewrite pr2 | pr3 | equalityCommutative (yesInjective pr) | NToBinNatZero a pr2 | NToBinNatZero b pr3 = refl
subtraction2 (succ a) b {t} pr | [] with≡ pr2 | (zero :: bl) with≡ pr3 with inspect (go zero [] bl)
subtraction2 (succ a) b {t} pr | [] with≡ pr2 | (zero :: bl) with≡ pr3 | no with≡ pr4 rewrite pr2 | pr3 | pr4 = exFalso (noNotYes pr)
subtraction2 (succ a) b {t} pr | [] with≡ pr2 | (zero :: bl) with≡ pr3 | yes x with≡ pr4 with goZeroEmpty bl pr4
subtraction2 (succ a) (succ b) {t} pr | [] with≡ pr2 | (zero :: bl) with≡ pr3 | yes x with≡ pr4 | r with goZeroEmpty' bl pr4
... | s rewrite pr2 | pr3 | pr4 | r | equalityCommutative (yesInjective pr) | NToBinNatZero a pr2 = exFalso (bad b pr3 r)
subtraction2 (succ a) b {t} pr | [] with≡ pr2 | (one :: bl) with≡ pr3 with inspect (go zero [] bl)
subtraction2 (succ a) b {t} pr | [] with≡ pr2 | (one :: bl) with≡ pr3 | no with≡ pr4 rewrite pr2 | pr3 | pr4 = exFalso (noNotYes pr)
subtraction2 (succ a) b {t} pr | [] with≡ pr2 | (one :: bl) with≡ pr3 | yes x with≡ pr4 with goZeroEmpty bl pr4
... | u with goZeroEmpty' bl pr4
... | v rewrite pr2 | pr3 | pr4 | u | NToBinNatZero a pr2 | lemma6 bl b u pr3 | equalityCommutative (yesInjective pr4) | equalityCommutative (yesInjective pr) = ans pr3
  where
    z : bl ≡ []
    z = lemma6 bl b u pr3
    ans : (NToBinNat b ≡ one :: bl) → b ≡ 1
    ans pr with applyEquality binNatToN pr
    ... | th rewrite z = transitivity (equalityCommutative (nToN b)) th
subtraction2 (succ a) b pr | (x :: y) with≡ pr2 with inspect (NToBinNat b)
subtraction2 (succ a) b pr | (zero :: y) with≡ pr2 | [] with≡ pr3 rewrite NToBinNatZero b pr3 | pr2 | pr3 | equalityCommutative (yesInjective pr) = applyEquality succ (transitivity (Semiring.sumZeroRight ℕSemiring _) (doubling a pr2))
subtraction2 (succ a) b pr | (one :: y) with≡ pr2 | [] with≡ pr3 rewrite NToBinNatZero b pr3 | pr2 | pr3 | equalityCommutative (yesInjective pr) = transitivity (Semiring.sumZeroRight ℕSemiring (binNatToN (incr y) +N (binNatToN (incr y) +N zero))) (equalityCommutative (transitivity (equalityCommutative (nToN (succ a))) (applyEquality binNatToN (transitivity (equalityCommutative (NToBinNatSucc a)) (applyEquality incr pr2)))))
subtraction2 (succ a) (succ b) {t} pr | (y :: ys) with≡ pr2 | (z :: zs) with≡ pr3 = transitivity (transitivity (Semiring.commutative ℕSemiring (binNatToN t) (succ b)) (applyEquality succ (transitivity (Semiring.commutative ℕSemiring b (binNatToN t)) (applyEquality (_+N b) (equalityCommutative (binNatToNIsCanonical t)))))) (applyEquality succ inter)
  where
    inter : binNatToN (canonical t) +N b ≡ a
    inter with inspect (go zero (NToBinNat a) (NToBinNat b))
    inter | no with≡ pr4 with goIncrIncr (NToBinNat a) (NToBinNat b)
    ... | f rewrite pr | pr4 = exFalso (noNotYes (equalityCommutative f))
    inter | yes x with≡ pr4 with goIncrIncr (NToBinNat a) (NToBinNat b)
    ... | f with subtraction2 a b {x} pr4
    ... | g = transitivity (applyEquality (_+N b) (transitivity (applyEquality binNatToN h) (binNatToNIsCanonical x))) g
      where
        h : (canonical t) ≡ (canonical x)
        h rewrite pr | pr4 = yesInjective f


subtraction2' : (a b : ℕ) {t : BinNat} → (NToBinNat a) -B (NToBinNat b) ≡ yes t → b ≤N a
subtraction2' a b {t} pr with subtraction2 a b pr
... | f with binNatToN t
subtraction2' a b {t} pr | f | zero = inr f
subtraction2' a b {t} pr | f | succ g = inl (le g f)

subtraction2'' : (a b : ℕ) → (pr : b ≤N a) → mapMaybe binNatToN ((NToBinNat a) -B (NToBinNat b)) ≡ yes (subtractionNResult.result (-N pr))
subtraction2'' a b pr with -N pr
subtraction2'' a b pr | record { result = result ; pr = subPr } with inspect (go zero (NToBinNat a) (NToBinNat b))
subtraction2'' a b (inl pr) | record { result = result ; pr = subPr } | no with≡ pr2 with subtraction (NToBinNat a) (NToBinNat b) pr2
... | bl rewrite nToN a | nToN b = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder pr bl))
subtraction2'' a b (inr pr) | record { result = result ; pr = subPr } | no with≡ pr2 with subtraction (NToBinNat a) (NToBinNat b) pr2
... | bl rewrite nToN a | nToN b | pr = exFalso (TotalOrder.irreflexive ℕTotalOrder bl)
subtraction2'' a b pr | record { result = result ; pr = subPr } | yes x with≡ pr2 with subtraction2 a b pr2
... | f rewrite pr2 | Semiring.commutative ℕSemiring (binNatToN x) b = applyEquality yes (canSubtractFromEqualityLeft {b} {binNatToN x} (transitivity f (equalityCommutative subPr)))
