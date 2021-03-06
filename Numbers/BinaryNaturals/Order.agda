{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas
open import Numbers.Naturals.Semiring
open import Numbers.BinaryNaturals.Definition
open import Orders.Partial.Definition
open import Orders.Total.Definition
open import Semirings.Definition

module Numbers.BinaryNaturals.Order where

data Compare : Set where
  Equal : Compare
  FirstLess : Compare
  FirstGreater : Compare

private
  badCompare : Equal ≡ FirstLess → False
  badCompare ()

  badCompare' : Equal ≡ FirstGreater → False
  badCompare' ()

  badCompare'' : FirstLess ≡ FirstGreater → False
  badCompare'' ()

_<BInherited_ : BinNat → BinNat → Compare
a <BInherited b with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
(a <BInherited b) | inl (inl x) = FirstLess
(a <BInherited b) | inl (inr x) = FirstGreater
(a <BInherited b) | inr x = Equal

private
  go<Bcomp : Compare → BinNat → BinNat → Compare
  go<Bcomp Equal [] [] = Equal
  go<Bcomp Equal [] (zero :: b) = go<Bcomp Equal [] b
  go<Bcomp Equal [] (one :: b) = FirstLess
  go<Bcomp Equal (zero :: a) [] = go<Bcomp Equal a []
  go<Bcomp Equal (zero :: a) (zero :: b) = go<Bcomp Equal a b
  go<Bcomp Equal (zero :: a) (one :: b) = go<Bcomp FirstLess a b
  go<Bcomp Equal (one :: a) [] = FirstGreater
  go<Bcomp Equal (one :: a) (zero :: b) = go<Bcomp FirstGreater a b
  go<Bcomp Equal (one :: a) (one :: b) = go<Bcomp Equal a b
  go<Bcomp FirstGreater [] [] = FirstGreater
  go<Bcomp FirstGreater [] (zero :: b) = go<Bcomp FirstGreater [] b
  go<Bcomp FirstGreater [] (one :: b) = FirstLess
  go<Bcomp FirstGreater (zero :: a) [] = FirstGreater
  go<Bcomp FirstGreater (zero :: a) (zero :: b) = go<Bcomp FirstGreater a b
  go<Bcomp FirstGreater (zero :: a) (one :: b) = go<Bcomp FirstLess a b
  go<Bcomp FirstGreater (one :: a) [] = FirstGreater
  go<Bcomp FirstGreater (one :: a) (zero :: b) = go<Bcomp FirstGreater a b
  go<Bcomp FirstGreater (one :: a) (one :: b) = go<Bcomp FirstGreater a b
  go<Bcomp FirstLess [] b = FirstLess
  go<Bcomp FirstLess (zero :: a) [] = go<Bcomp FirstLess a []
  go<Bcomp FirstLess (one :: a) [] = FirstGreater
  go<Bcomp FirstLess (zero :: a) (zero :: b) = go<Bcomp FirstLess a b
  go<Bcomp FirstLess (zero :: a) (one :: b) = go<Bcomp FirstLess a b
  go<Bcomp FirstLess (one :: a) (zero :: b) = go<Bcomp FirstGreater a b
  go<Bcomp FirstLess (one :: a) (one :: b) = go<Bcomp FirstLess a b

_<Bcomp_ : BinNat → BinNat → Compare
a <Bcomp b = go<Bcomp Equal a b

private
  lemma1 : {s : Compare} → (n : BinNat) → go<Bcomp s n n ≡ s
  lemma1 {Equal} [] = refl
  lemma1 {Equal} (zero :: n) = lemma1 n
  lemma1 {Equal} (one :: n) = lemma1 n
  lemma1 {FirstLess} [] = refl
  lemma1 {FirstLess} (zero :: n) = lemma1 n
  lemma1 {FirstLess} (one :: n) = lemma1 n
  lemma1 {FirstGreater} [] = refl
  lemma1 {FirstGreater} (zero :: n) = lemma1 n
  lemma1 {FirstGreater} (one :: n) = lemma1 n

  lemma : {s : Compare} → (n : BinNat) → go<Bcomp s (incr n) n ≡ FirstGreater
  lemma {Equal} [] = refl
  lemma {Equal} (zero :: n) = lemma1 n
  lemma {Equal} (one :: n) = lemma {FirstLess} n
  lemma {FirstLess} [] = refl
  lemma {FirstLess} (zero :: n) = lemma1 n
  lemma {FirstLess} (one :: n) = lemma {FirstLess} n
  lemma {FirstGreater} [] = refl
  lemma {FirstGreater} (zero :: n) = lemma1 {FirstGreater} n
  lemma {FirstGreater} (one :: n) = lemma {FirstLess} n

  succLess : (n : ℕ) → (NToBinNat (succ n)) <Bcomp (NToBinNat n) ≡ FirstGreater
  succLess zero = refl
  succLess (succ n) with NToBinNat n
  succLess (succ n) | [] = refl
  succLess (succ n) | zero :: bl = lemma {FirstLess} bl
  succLess (succ n) | one :: bl = lemma1 {FirstGreater} (incr bl)

  compareRefl : (n : BinNat) → n <Bcomp n ≡ Equal
  compareRefl [] = refl
  compareRefl (zero :: n) = compareRefl n
  compareRefl (one :: n) = compareRefl n

  zeroLess : (n : BinNat) → ((canonical n ≡ []) → False) → [] <Bcomp n ≡ FirstLess
  zeroLess [] pr = exFalso (pr refl)
  zeroLess (zero :: n) pr with inspect (canonical n)
  zeroLess (zero :: n) pr | [] with≡ x rewrite x = exFalso (pr refl)
  zeroLess (zero :: n) pr | (x₁ :: y) with≡ x = zeroLess n λ i → nonEmptyNotEmpty (transitivity (equalityCommutative x) i)
  zeroLess (one :: n) pr = refl

  zeroLess' : (n : BinNat) → ((canonical n ≡ []) → False) → n <Bcomp [] ≡ FirstGreater
  zeroLess' [] pr = exFalso (pr refl)
  zeroLess' (zero :: n) pr with inspect (canonical n)
  zeroLess' (zero :: n) pr | [] with≡ x rewrite x = exFalso (pr refl)
  zeroLess' (zero :: n) pr | (x₁ :: y) with≡ x = zeroLess' n (λ i → nonEmptyNotEmpty (transitivity (equalityCommutative x) i))
  zeroLess' (one :: n) pr = refl

abstract
  canonicalFirst : (n m : BinNat) (state : Compare) → go<Bcomp state n m ≡ go<Bcomp state (canonical n) m
  canonicalFirst [] m Equal = refl
  canonicalFirst (zero :: n) m Equal with inspect (canonical n)
  canonicalFirst (zero :: n) [] Equal | [] with≡ x rewrite x = transitivity (canonicalFirst n [] Equal) (applyEquality (λ i → go<Bcomp Equal i []) {canonical n} x)
  canonicalFirst (zero :: n) (zero :: ms) Equal | [] with≡ x rewrite x | canonicalFirst n ms Equal | x = refl
  canonicalFirst (zero :: n) (one :: ms) Equal | [] with≡ x rewrite x | canonicalFirst n ms FirstLess | x = refl
  canonicalFirst (zero :: n) [] Equal | (x₁ :: y) with≡ x rewrite x | canonicalFirst n [] Equal | x = refl
  canonicalFirst (zero :: n) (zero :: ms) Equal | (x₁ :: y) with≡ x rewrite x | canonicalFirst n ms Equal | x = refl
  canonicalFirst (zero :: n) (one :: ms) Equal | (x₁ :: y) with≡ x rewrite x | canonicalFirst n ms FirstLess | x = refl
  canonicalFirst (one :: n) [] Equal = refl
  canonicalFirst (one :: n) (zero :: m) Equal = canonicalFirst n m FirstGreater
  canonicalFirst (one :: n) (one :: m) Equal = canonicalFirst n m Equal
  canonicalFirst [] m FirstLess = refl
  canonicalFirst (zero :: n) [] FirstLess with inspect (canonical n)
  canonicalFirst (zero :: n) [] FirstLess | [] with≡ x rewrite x | canonicalFirst n [] FirstLess | x = refl
  canonicalFirst (zero :: n) [] FirstLess | (x₁ :: y) with≡ x rewrite x | canonicalFirst n [] FirstLess | x = refl
  canonicalFirst (zero :: n) (zero :: m) FirstLess with inspect (canonical n)
  canonicalFirst (zero :: n) (zero :: m) FirstLess | [] with≡ x rewrite x | canonicalFirst n m FirstLess | x = refl
  canonicalFirst (zero :: n) (zero :: m) FirstLess | (x₁ :: y) with≡ x rewrite x | canonicalFirst n m FirstLess | x = refl
  canonicalFirst (zero :: n) (one :: m) FirstLess with inspect (canonical n)
  canonicalFirst (zero :: n) (one :: m) FirstLess | [] with≡ x rewrite x | canonicalFirst n m FirstLess | x = refl
  canonicalFirst (zero :: n) (one :: m) FirstLess | (x₁ :: y) with≡ x rewrite x | canonicalFirst n m FirstLess | x = refl
  canonicalFirst (one :: n) [] FirstLess = refl
  canonicalFirst (one :: n) (zero :: m) FirstLess = canonicalFirst n m FirstGreater
  canonicalFirst (one :: n) (one :: m) FirstLess = canonicalFirst n m FirstLess
  canonicalFirst [] m FirstGreater = refl
  canonicalFirst (zero :: n) m FirstGreater with inspect (canonical n)
  canonicalFirst (zero :: n) [] FirstGreater | [] with≡ x rewrite x = refl
  canonicalFirst (zero :: n) (zero :: ms) FirstGreater | [] with≡ x rewrite x | canonicalFirst n ms FirstGreater | x = refl
  canonicalFirst (zero :: n) (one :: ms) FirstGreater | [] with≡ x rewrite x | canonicalFirst n ms FirstLess | x = refl
  canonicalFirst (zero :: n) [] FirstGreater | (x₁ :: y) with≡ x rewrite x = refl
  canonicalFirst (zero :: n) (zero :: ms) FirstGreater | (x₁ :: y) with≡ x rewrite x | canonicalFirst n ms FirstGreater | x = refl
  canonicalFirst (zero :: n) (one :: ms) FirstGreater | (x₁ :: y) with≡ x rewrite x | canonicalFirst n ms FirstLess | x = refl
  canonicalFirst (one :: n) [] FirstGreater = refl
  canonicalFirst (one :: n) (zero :: m) FirstGreater = canonicalFirst n m FirstGreater
  canonicalFirst (one :: n) (one :: m) FirstGreater = canonicalFirst n m FirstGreater

private
  greater0Lemma : (n : BinNat) → go<Bcomp FirstGreater n [] ≡ FirstGreater
  greater0Lemma [] = refl
  greater0Lemma (zero :: n) = refl
  greater0Lemma (one :: n) = refl

  canonicalSecond : (n m : BinNat) (state : Compare) → go<Bcomp state n m ≡ go<Bcomp state n (canonical m)
  canonicalSecond n [] Equal = refl
  canonicalSecond [] (zero :: m) Equal with inspect (canonical m)
  canonicalSecond [] (zero :: m) Equal | [] with≡ x rewrite x | canonicalSecond [] m Equal | x = refl
  canonicalSecond [] (zero :: m) Equal | (x₁ :: y) with≡ x rewrite x | canonicalSecond [] m Equal | x = refl
  canonicalSecond (zero :: n) (zero :: m) Equal with inspect (canonical m)
  canonicalSecond (zero :: n) (zero :: m) Equal | [] with≡ x rewrite x | canonicalSecond n m Equal | x = refl
  canonicalSecond (zero :: n) (zero :: m) Equal | (x₁ :: y) with≡ x rewrite x | canonicalSecond n m Equal | x = refl
  canonicalSecond (one :: n) (zero :: m) Equal with inspect (canonical m)
  canonicalSecond (one :: n) (zero :: m) Equal | [] with≡ x rewrite x | canonicalSecond n m FirstGreater | x = greater0Lemma n
  canonicalSecond (one :: n) (zero :: m) Equal | (x₁ :: y) with≡ x rewrite x | canonicalSecond n m FirstGreater | x = refl
  canonicalSecond [] (one :: m) Equal = refl
  canonicalSecond (zero :: n) (one :: m) Equal = canonicalSecond n m FirstLess
  canonicalSecond (one :: n) (one :: m) Equal = canonicalSecond n m Equal
  canonicalSecond n [] FirstLess = refl
  canonicalSecond [] (zero :: m) FirstLess = refl
  canonicalSecond (x :: n) (zero :: m) FirstLess with inspect (canonical m)
  canonicalSecond (zero :: n) (zero :: m) FirstLess | [] with≡ x rewrite x | canonicalSecond n m FirstLess | x = refl
  canonicalSecond (one :: n) (zero :: m) FirstLess | [] with≡ x rewrite x | canonicalSecond n m FirstGreater | x = greater0Lemma n
  canonicalSecond (zero :: n) (zero :: m) FirstLess | (x₁ :: bl) with≡ pr rewrite pr | canonicalSecond n m FirstLess | pr = refl
  canonicalSecond (one :: n) (zero :: m) FirstLess | (x₁ :: bl) with≡ pr rewrite pr | canonicalSecond n m FirstGreater | pr = refl
  canonicalSecond [] (one :: m) FirstLess = refl
  canonicalSecond (zero :: n) (one :: m) FirstLess = canonicalSecond n m FirstLess
  canonicalSecond (one :: n) (one :: m) FirstLess = canonicalSecond n m FirstLess
  canonicalSecond n [] FirstGreater = refl
  canonicalSecond [] (zero :: m) FirstGreater with inspect (canonical m)
  canonicalSecond [] (zero :: m) FirstGreater | [] with≡ x rewrite x | canonicalSecond [] m FirstGreater | x = refl
  canonicalSecond [] (zero :: m) FirstGreater | (x₁ :: y) with≡ x rewrite x | canonicalSecond [] m FirstGreater | x = refl
  canonicalSecond (zero :: n) (zero :: m) FirstGreater with inspect (canonical m)
  canonicalSecond (zero :: n) (zero :: m) FirstGreater | [] with≡ x rewrite x | canonicalSecond n m FirstGreater | x = greater0Lemma n
  canonicalSecond (zero :: n) (zero :: m) FirstGreater | (x₁ :: y) with≡ x rewrite x | canonicalSecond n m FirstGreater | x = refl
  canonicalSecond (one :: n) (zero :: m) FirstGreater with inspect (canonical m)
  canonicalSecond (one :: n) (zero :: m) FirstGreater | [] with≡ x rewrite x | canonicalSecond n m FirstGreater | x = greater0Lemma n
  canonicalSecond (one :: n) (zero :: m) FirstGreater | (x₁ :: y) with≡ x rewrite x | canonicalSecond n m FirstGreater | x = refl
  canonicalSecond [] (one :: m) FirstGreater = refl
  canonicalSecond (zero :: n) (one :: m) FirstGreater = canonicalSecond n m FirstLess
  canonicalSecond (one :: n) (one :: m) FirstGreater = canonicalSecond n m FirstGreater

  equalContaminated : (n m : BinNat) → go<Bcomp FirstLess n m ≡ Equal → False
  equalContaminated' : (n m : BinNat) → go<Bcomp FirstGreater n m ≡ Equal → False

  equalContaminated (zero :: n) [] pr = equalContaminated n [] pr
  equalContaminated (zero :: n) (zero :: m) pr = equalContaminated n m pr
  equalContaminated (zero :: n) (one :: m) pr = equalContaminated n m pr
  equalContaminated (one :: n) (zero :: m) pr = equalContaminated' n m pr
  equalContaminated (one :: n) (one :: m) pr = equalContaminated n m pr

  equalContaminated' [] (zero :: m) pr = equalContaminated' [] m pr
  equalContaminated' (zero :: n) (zero :: m) pr = equalContaminated' n m pr
  equalContaminated' (zero :: n) (one :: m) pr = equalContaminated n m pr
  equalContaminated' (one :: n) (zero :: m) pr = equalContaminated' n m pr
  equalContaminated' (one :: n) (one :: m) pr = equalContaminated' n m pr

  comparisonEqual : (a b : BinNat) → (a <Bcomp b ≡ Equal) → canonical a ≡ canonical b
  comparisonEqual [] [] pr = refl
  comparisonEqual [] (zero :: b) pr with inspect (canonical b)
  comparisonEqual [] (zero :: b) pr | [] with≡ p rewrite p = refl
  comparisonEqual [] (zero :: b) pr | (x :: r) with≡ p rewrite zeroLess b (λ i → nonEmptyNotEmpty (transitivity (equalityCommutative p) i)) = exFalso (badCompare (equalityCommutative pr))
  comparisonEqual (zero :: a) [] pr with inspect (canonical a)
  comparisonEqual (zero :: a) [] pr | [] with≡ x rewrite x = refl
  comparisonEqual (zero :: a) [] pr | (x₁ :: y) with≡ x rewrite zeroLess' a (λ i → nonEmptyNotEmpty (transitivity (equalityCommutative x) i)) = exFalso (badCompare' (equalityCommutative pr))
  comparisonEqual (zero :: a) (zero :: b) pr with inspect (canonical a)
  comparisonEqual (zero :: a) (zero :: b) pr | [] with≡ x with inspect (canonical b)
  comparisonEqual (zero :: a) (zero :: b) pr | [] with≡ pr2 | [] with≡ pr3 rewrite pr2 | pr3 = refl
  comparisonEqual (zero :: a) (zero :: b) pr | [] with≡ pr2 | (x₂ :: y) with≡ pr3 rewrite pr2 | pr3 | comparisonEqual a b pr = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative pr3) pr2))
  comparisonEqual (zero :: a) (zero :: b) pr | (c :: cs) with≡ pr2 with inspect (canonical b)
  comparisonEqual (zero :: a) (zero :: b) pr | (c :: cs) with≡ pr2 | [] with≡ pr3 rewrite pr2 | pr3 | comparisonEqual a b pr = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative pr2) pr3))
  comparisonEqual (zero :: a) (zero :: b) pr | (c :: cs) with≡ pr2 | (x₁ :: y) with≡ pr3 rewrite pr2 | pr3 | comparisonEqual a b pr = applyEquality (zero ::_) (transitivity (equalityCommutative pr2) pr3)
  comparisonEqual (zero :: a) (one :: b) pr = exFalso (equalContaminated a b pr)
  comparisonEqual (one :: a) (zero :: b) pr = exFalso (equalContaminated' a b pr)
  comparisonEqual (one :: a) (one :: b) pr = applyEquality (one ::_) (comparisonEqual a b pr)

  equalSymmetric : (n m : BinNat) → n <Bcomp m ≡ Equal → m <Bcomp n ≡ Equal
  equalSymmetric [] [] n=m = refl
  equalSymmetric [] (zero :: m) n=m rewrite equalSymmetric [] m n=m = refl
  equalSymmetric (zero :: n) [] n=m rewrite equalSymmetric n [] n=m = refl
  equalSymmetric (zero :: n) (zero :: m) n=m = equalSymmetric n m n=m
  equalSymmetric (zero :: n) (one :: m) n=m = exFalso (equalContaminated n m n=m)
  equalSymmetric (one :: n) (zero :: m) n=m = exFalso (equalContaminated' n m n=m)
  equalSymmetric (one :: n) (one :: m) n=m = equalSymmetric n m n=m

  equalToFirstGreater : (state : Compare) → (a b : BinNat) → go<Bcomp Equal a b ≡ FirstGreater → go<Bcomp state a b ≡ FirstGreater
  equalToFirstGreater FirstGreater [] (zero :: b) pr = equalToFirstGreater FirstGreater [] b pr
  equalToFirstGreater FirstGreater (zero :: a) [] pr = refl
  equalToFirstGreater FirstGreater (zero :: a) (zero :: b) pr = equalToFirstGreater FirstGreater a b pr
  equalToFirstGreater FirstGreater (zero :: a) (one :: b) pr = pr
  equalToFirstGreater FirstGreater (one :: a) [] pr = refl
  equalToFirstGreater FirstGreater (one :: a) (zero :: b) pr = pr
  equalToFirstGreater FirstGreater (one :: a) (one :: b) pr = equalToFirstGreater FirstGreater a b pr
  equalToFirstGreater Equal a b pr = pr
  equalToFirstGreater FirstLess [] (zero :: b) pr = equalToFirstGreater FirstLess [] b pr
  equalToFirstGreater FirstLess (zero :: a) [] pr = equalToFirstGreater FirstLess a [] pr
  equalToFirstGreater FirstLess (zero :: a) (zero :: b) pr = equalToFirstGreater FirstLess a b pr
  equalToFirstGreater FirstLess (zero :: a) (one :: b) pr = pr
  equalToFirstGreater FirstLess (one :: a) [] pr = refl
  equalToFirstGreater FirstLess (one :: a) (zero :: b) pr = pr
  equalToFirstGreater FirstLess (one :: a) (one :: b) pr = equalToFirstGreater FirstLess a b pr

  equalToFirstLess : (state : Compare) → (a b : BinNat) → go<Bcomp Equal a b ≡ FirstLess → go<Bcomp state a b ≡ FirstLess
  equalToFirstLess FirstLess [] b pr = refl
  equalToFirstLess FirstLess (zero :: a) [] pr = equalToFirstLess FirstLess a [] pr
  equalToFirstLess FirstLess (zero :: a) (zero :: b) pr = equalToFirstLess FirstLess a b pr
  equalToFirstLess FirstLess (zero :: a) (one :: b) pr = pr
  equalToFirstLess FirstLess (one :: a) (zero :: b) pr = pr
  equalToFirstLess FirstLess (one :: a) (one :: b) pr = equalToFirstLess FirstLess a b pr
  equalToFirstLess Equal a b pr = pr
  equalToFirstLess FirstGreater [] (zero :: b) pr = equalToFirstLess FirstGreater [] b pr
  equalToFirstLess FirstGreater [] (one :: b) pr = refl
  equalToFirstLess FirstGreater (zero :: a) [] pr = transitivity (t a) (equalToFirstLess FirstGreater a [] pr)
    where
      t : (a : BinNat) → FirstGreater ≡ go<Bcomp FirstGreater a []
      t [] = refl
      t (zero :: a) = refl
      t (one :: a) = refl
  equalToFirstLess FirstGreater (zero :: a) (zero :: b) pr = equalToFirstLess FirstGreater a b pr
  equalToFirstLess FirstGreater (zero :: a) (one :: b) pr = pr
  equalToFirstLess FirstGreater (one :: a) (zero :: b) pr = pr
  equalToFirstLess FirstGreater (one :: a) (one :: b) pr = equalToFirstLess FirstGreater a b pr

  zeroNotSucc : (n : ℕ) (b : BinNat) → (canonical b ≡ []) → (binNatToN b ≡ succ n) → False
  zeroNotSucc n b b=0 b>0 rewrite binNatToNZero' b b=0 = naughtE b>0

  chopFirstBit : (m n : BinNat) {b : Bit} (s : Compare) → go<Bcomp s (b :: m) (b :: n) ≡ go<Bcomp s m n
  chopFirstBit m n {zero} Equal = refl
  chopFirstBit m n {one} Equal = refl
  chopFirstBit m n {zero} FirstLess = refl
  chopFirstBit m n {one} FirstLess = refl
  chopFirstBit m n {zero} FirstGreater = refl
  chopFirstBit m n {one} FirstGreater = refl

  chopDouble : (a b : BinNat) (i : Bit) → (i :: a) <BInherited (i :: b) ≡ a <BInherited b
  chopDouble a b i with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
  chopDouble a b zero | inl (inl a<b) with TotalOrder.totality ℕTotalOrder (2 *N binNatToN a) (2 *N binNatToN b)
  chopDouble a b zero | inl (inl a<b) | inl (inl x) = refl
  chopDouble a b zero | inl (inl a<b) | inl (inr b<a) = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder b<a (lessRespectsMultiplicationLeft (binNatToN a) (binNatToN b) 2 a<b (le 1 refl))))
  chopDouble a b zero | inl (inl a<b) | inr a=b rewrite productCancelsLeft 2 (binNatToN a) (binNatToN b) (le 1 refl) a=b = exFalso (TotalOrder.irreflexive ℕTotalOrder a<b)
  chopDouble a b one | inl (inl a<b) with TotalOrder.totality ℕTotalOrder (2 *N binNatToN a) (2 *N binNatToN b)
  chopDouble a b one | inl (inl a<b) | inl (inl 2a<2b) = refl
  chopDouble a b one | inl (inl a<b) | inl (inr 2b<2a) = exFalso (TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive (ℕTotalOrder) a<b (cancelInequalityLeft {2} 2b<2a)))
  chopDouble a b one | inl (inl a<b) | inr 2a=2b rewrite productCancelsLeft 2 (binNatToN a) (binNatToN b) (le 1 refl) 2a=2b = exFalso (TotalOrder.irreflexive (ℕTotalOrder) a<b)
  chopDouble a b zero | inl (inr b<a) with TotalOrder.totality ℕTotalOrder (2 *N binNatToN a) (2 *N binNatToN b)
  chopDouble a b zero | inl (inr b<a) | inl (inl 2a<2b) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) b<a (cancelInequalityLeft {2} {binNatToN a} {binNatToN b} 2a<2b)))
  chopDouble a b zero | inl (inr b<a) | inl (inr 2b<2a) = refl
  chopDouble a b zero | inl (inr b<a) | inr 2a=2b rewrite productCancelsLeft 2 (binNatToN a) (binNatToN b) (le 1 refl) 2a=2b = exFalso (TotalOrder.irreflexive (ℕTotalOrder) b<a)
  chopDouble a b one | inl (inr b<a) with TotalOrder.totality ℕTotalOrder (2 *N binNatToN a) (2 *N binNatToN b)
  chopDouble a b one | inl (inr b<a) | inl (inl 2a<2b) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) b<a (cancelInequalityLeft {2} 2a<2b)))
  chopDouble a b one | inl (inr b<a) | inl (inr x) = refl
  chopDouble a b one | inl (inr b<a) | inr 2a=2b rewrite productCancelsLeft 2 (binNatToN a) (binNatToN b) (le 1 refl) 2a=2b = exFalso (TotalOrder.irreflexive (ℕTotalOrder) b<a)
  chopDouble a b i | inr x with TotalOrder.totality ℕTotalOrder (binNatToN (i :: a)) (binNatToN (i :: b))
  chopDouble a b zero | inr a=b | inl (inl a<b) rewrite a=b = exFalso (TotalOrder.irreflexive (ℕTotalOrder) a<b)
  chopDouble a b one | inr a=b | inl (inl a<b) rewrite a=b = exFalso (TotalOrder.irreflexive (ℕTotalOrder) a<b)
  chopDouble a b zero | inr a=b | inl (inr b<a) rewrite a=b = exFalso (TotalOrder.irreflexive (ℕTotalOrder) b<a)
  chopDouble a b one | inr a=b | inl (inr b<a) rewrite a=b = exFalso (TotalOrder.irreflexive (ℕTotalOrder) b<a)
  chopDouble a b _ | inr a=b | inr x = refl

  succNotLess : {n : ℕ} → succ n <N n → False
  succNotLess {succ n} (le x proof) = succNotLess {n} (le x (succInjective (transitivity (applyEquality succ (transitivity (Semiring.commutative ℕSemiring (succ x) (succ n)) (transitivity (applyEquality succ (transitivity (Semiring.commutative ℕSemiring n (succ x)) (applyEquality succ (Semiring.commutative ℕSemiring x n)))) (Semiring.commutative ℕSemiring (succ (succ n)) x)))) proof)))

<BIsInherited : (a b : BinNat) → a <BInherited b ≡ a <Bcomp b
<BIsInherited [] b with TotalOrder.totality ℕTotalOrder 0 (binNatToN b)
<BIsInherited [] b | inl (inl x) with inspect (binNatToN b)
<BIsInherited [] b | inl (inl x) | 0 with≡ pr rewrite binNatToNZero b pr | pr = exFalso (TotalOrder.irreflexive (ℕTotalOrder) x)
<BIsInherited [] b | inl (inl x) | (succ bl) with≡ pr rewrite pr = equalityCommutative (zeroLess b λ p → zeroNotSucc bl b p pr)
<BIsInherited [] b | inr 0=b rewrite canonicalSecond [] b Equal | binNatToNZero b (equalityCommutative 0=b) = refl
<BIsInherited (a :: as) [] with TotalOrder.totality ℕTotalOrder (binNatToN (a :: as)) 0
<BIsInherited (a :: as) [] | inl (inr x) with inspect (binNatToN (a :: as))
<BIsInherited (a :: as) [] | inl (inr x) | zero with≡ pr rewrite binNatToNZero (a :: as) pr | pr = exFalso (TotalOrder.irreflexive (ℕTotalOrder) x)
<BIsInherited (a :: as) [] | inl (inr x) | succ y with≡ pr rewrite pr = equalityCommutative (zeroLess' (a :: as) λ i → zeroNotSucc y (a :: as) i pr)
<BIsInherited (a :: as) [] | inr x rewrite canonicalFirst (a :: as) [] Equal | binNatToNZero (a :: as) x = refl
<BIsInherited (zero :: a) (zero :: b) = transitivity (chopDouble a b zero) (<BIsInherited a b)
<BIsInherited (zero :: a) (one :: b) with TotalOrder.totality ℕTotalOrder (binNatToN (zero :: a)) (binNatToN (one :: b))
<BIsInherited (zero :: a) (one :: b) | inl (inl 2a<2b+1) with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
<BIsInherited (zero :: a) (one :: b) | inl (inl 2a<2b+1) | inl (inl a<b) = equalityCommutative (equalToFirstLess FirstLess a b (equalityCommutative indHyp))
    where
      t : a <BInherited b ≡ FirstLess
      t with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
      t | inl (inl x) = refl
      t | inl (inr x) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) x a<b))
      t | inr x rewrite x = exFalso (TotalOrder.irreflexive (ℕTotalOrder) a<b)
      indHyp : FirstLess ≡ go<Bcomp Equal a b
      indHyp = transitivity (equalityCommutative t) (<BIsInherited a b)
<BIsInherited (zero :: a) (one :: b) | inl (inl 2a<2b+1) | inl (inr b<a) = exFalso (noIntegersBetweenXAndSuccX {2 *N binNatToN a} (2 *N binNatToN b) (lessRespectsMultiplicationLeft (binNatToN b) (binNatToN a) 2 b<a (le 1 refl)) 2a<2b+1)
<BIsInherited (zero :: a) (one :: b) | inl (inl 2a<2b+1) | inr a=b rewrite a=b | canonicalFirst a b FirstLess | canonicalSecond (canonical a) b FirstLess | transitivity (equalityCommutative (binToBin a)) (transitivity (applyEquality NToBinNat a=b) (binToBin b)) = equalityCommutative (lemma1 (canonical b))
<BIsInherited (zero :: a) (one :: b) | inl (inr 2b+1<2a) with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
<BIsInherited (zero :: a) (one :: b) | inl (inr 2b+1<2a) | inl (inl a<b) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) 2b+1<2a (TotalOrder.<Transitive (ℕTotalOrder) (lessRespectsMultiplicationLeft (binNatToN a) (binNatToN b) 2 a<b (le 1 refl)) (le zero refl))))
<BIsInherited (zero :: a) (one :: b) | inl (inr 2b+1<2a) | inl (inr b<a) = equalityCommutative (equalToFirstGreater FirstLess a b (equalityCommutative indHyp))
  where
    t : a <BInherited b ≡ FirstGreater
    t with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
    t | inl (inl x) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) x b<a))
    t | inl (inr x) = refl
    t | inr x rewrite x = exFalso (TotalOrder.irreflexive (ℕTotalOrder) b<a)
    indHyp : FirstGreater ≡ go<Bcomp Equal a b
    indHyp = transitivity (equalityCommutative t) (<BIsInherited a b)
<BIsInherited (zero :: a) (one :: b) | inl (inr 2b+1<2a) | inr a=b rewrite a=b = exFalso (succNotLess 2b+1<2a)
<BIsInherited (zero :: a) (one :: b) | inr 2a=2b+1 = exFalso (parity (binNatToN b) (binNatToN a) (equalityCommutative 2a=2b+1))
<BIsInherited (one :: a) (zero :: b) with TotalOrder.totality ℕTotalOrder (binNatToN (one :: a)) (binNatToN (zero :: b))
<BIsInherited (one :: a) (zero :: b) | inl (inl 2a+1<2b) with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
<BIsInherited (one :: a) (zero :: b) | inl (inl 2a+1<2b) | inl (inl a<b) = equalityCommutative (equalToFirstLess FirstGreater a b (equalityCommutative indHyp))
  where
    t : a <BInherited b ≡ FirstLess
    t with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
    t | inl (inr x) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) x a<b))
    t | inl (inl x) = refl
    t | inr x rewrite x = exFalso (TotalOrder.irreflexive (ℕTotalOrder) a<b)
    indHyp : FirstLess ≡ go<Bcomp Equal a b
    indHyp = transitivity (equalityCommutative t) (<BIsInherited a b)
<BIsInherited (one :: a) (zero :: b) | inl (inl 2a+1<2b) | inl (inr b<a) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) 2a+1<2b (TotalOrder.<Transitive (ℕTotalOrder) (lessRespectsMultiplicationLeft (binNatToN b) (binNatToN a) 2 b<a (le 1 refl)) (le zero refl))))
<BIsInherited (one :: a) (zero :: b) | inl (inl 2a+1<2b) | inr a=b rewrite a=b = exFalso (succNotLess 2a+1<2b)
<BIsInherited (one :: a) (zero :: b) | inl (inr 2b<2a+1) with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
<BIsInherited (one :: a) (zero :: b) | inl (inr 2b<2a+1) | inl (inl a<b) = exFalso (noIntegersBetweenXAndSuccX {2 *N binNatToN b} (2 *N binNatToN a) (lessRespectsMultiplicationLeft (binNatToN a) (binNatToN b) 2 a<b (le 1 refl)) 2b<2a+1)
<BIsInherited (one :: a) (zero :: b) | inl (inr 2b<2a+1) | inl (inr b<a) = equalityCommutative (equalToFirstGreater FirstGreater a b (equalityCommutative indHyp))
  where
    t : a <BInherited b ≡ FirstGreater
    t with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
    t | inl (inl x) = exFalso (TotalOrder.irreflexive (ℕTotalOrder) (TotalOrder.<Transitive (ℕTotalOrder) x b<a))
    t | inl (inr x) = refl
    t | inr x rewrite x = exFalso (TotalOrder.irreflexive (ℕTotalOrder) b<a)
    indHyp : FirstGreater ≡ go<Bcomp Equal a b
    indHyp = transitivity (equalityCommutative t) (<BIsInherited a b)
<BIsInherited (one :: a) (zero :: b) | inl (inr 2b<2a+1) | inr a=b rewrite a=b | canonicalFirst a b FirstGreater | canonicalSecond (canonical a) b FirstGreater | transitivity (equalityCommutative (binToBin a)) (transitivity (applyEquality NToBinNat a=b) (binToBin b)) = equalityCommutative (lemma1 (canonical b))
<BIsInherited (one :: a) (zero :: b) | inr x = exFalso (parity (binNatToN a) (binNatToN b) x)
<BIsInherited (one :: a) (one :: b) = transitivity (chopDouble a b one) (<BIsInherited a b)

_<B_ : BinNat → BinNat → Set
a <B b = (a <Bcomp b) ≡ FirstLess

translate : (a b : BinNat) → (a <B b) → (binNatToN a) <N (binNatToN b)
translate a b a<b with <BIsInherited a b
... | r with TotalOrder.totality ℕTotalOrder (binNatToN a) (binNatToN b)
... | inl (inl x) = x
... | inl (inr x) = exFalso (badCompare'' (transitivity (equalityCommutative a<b) (equalityCommutative r)))
... | inr x = exFalso (badCompare (transitivity r a<b))

private
  totality : (a b : BinNat) → ((a <B b) || (b <B a)) || (canonical a ≡ canonical b)
  totality [] [] = inr refl
  totality [] (zero :: b) with totality [] b
  ... | inl (inl x) = inl (inl x)
  ... | inl (inr x) = inl (inr x)
  ... | inr x with canonical b
  ... | [] = inr refl
  totality [] (one :: b) = inl (inl refl)
  totality (zero :: a) [] with totality a []
  ... | inl (inl x) = inl (inl x)
  ... | inl (inr x) = inl (inr x)
  ... | inr x with canonical a
  ... | [] = inr refl
  totality (zero :: a) (zero :: b) with totality a b
  ... | inl (inl x) = inl (inl x)
  ... | inl (inr x) = inl (inr x)
  ... | inr x rewrite x = inr refl
  totality (zero :: a) (one :: b) with totality a b
  ... | inl (inl x) = inl (inl (equalToFirstLess FirstLess a b x))
  ... | inr x rewrite canonicalSecond a b FirstLess | canonicalFirst a (canonical b) FirstLess | x = inl (inl (lemma1 (canonical b)))
  ... | inl (inr x) with equalToFirstLess FirstGreater b a x
  ... | r = inl (inr r)
  totality (one :: a) [] = inl (inr refl)
  totality (one :: a) (zero :: b) with totality a b
  ... | inr x rewrite canonicalSecond b a FirstLess | canonicalFirst b (canonical a) FirstLess | x = inl (inr (lemma1 (canonical b)))
  ... | inl (inr x) = inl (inr (equalToFirstLess FirstLess b a x))
  ... | inl (inl x) with equalToFirstLess FirstGreater a b x
  ... | r = inl (inl r)
  totality (one :: a) (one :: b) with totality a b
  ... | inl (inl x) = inl (inl x)
  ... | inl (inr x) = inl (inr x)
  ... | inr x rewrite x = inr refl

translate' : (a b : ℕ) → (a <N b) → (NToBinNat a) <B (NToBinNat b)
translate' a b a<b with totality (NToBinNat a) (NToBinNat b)
... | inl (inl x) = x
... | inl (inr x) with translate (NToBinNat b) (NToBinNat a) x
... | m = exFalso (lessIrreflexive (lessTransitive a<b (identityOfIndiscernablesLeft _<N_ (identityOfIndiscernablesRight _<N_ m (nToN a)) (nToN b))))
translate' a b a<b | inr x rewrite NToBinNatInj a b x = exFalso (lessIrreflexive a<b)

private
  <BTransitive : (a b c : BinNat) → (a <B b) → (b <B c) → a <B c
  <BTransitive a b c a<b b<c with translate' (binNatToN a) (binNatToN c) (PartialOrder.<Transitive (TotalOrder.order ℕTotalOrder) (translate a b a<b) (translate b c b<c))
  ... | r rewrite binToBin a | binToBin c = transitivity (canonicalFirst a c Equal) (transitivity (canonicalSecond (canonical a) c Equal) r)

-- This order fails to be total because [] is not literally equal to 0::[] .
BinNatOrder : PartialOrder BinNat
PartialOrder._<_ (BinNatOrder) = _<B_
PartialOrder.irreflexive (BinNatOrder) {x} bad = badCompare (transitivity (equalityCommutative (compareRefl x)) bad)
PartialOrder.<Transitive (BinNatOrder) {a} {b} {c} a<b b<c = <BTransitive a b c a<b b<c
