{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Lists.Lists
open import Numbers.BinaryNaturals.Definition
open import Maybe

module Numbers.BinaryNaturals.SubtractionGo where

  go : Bit → BinNat → BinNat → Maybe BinNat
  go zero [] [] = yes []
  go one [] [] = no
  go zero [] (zero :: b) = go zero [] b
  go zero [] (one :: b) = no
  go one [] (x :: b) = no
  go zero (zero :: a) [] = yes (zero :: a)
  go one (zero :: a) [] = mapMaybe (one ::_) (go one a [])
  go zero (zero :: a) (zero :: b) = mapMaybe (zero ::_) (go zero a b)
  go one (zero :: a) (zero :: b) = mapMaybe (one ::_) (go one a b)
  go zero (zero :: a) (one :: b) = mapMaybe (one ::_) (go one a b)
  go one (zero :: a) (one :: b) = mapMaybe (zero ::_) (go one a b)
  go zero (one :: a) [] = yes (one :: a)
  go zero (one :: a) (zero :: b) = mapMaybe (one ::_) (go zero a b)
  go zero (one :: a) (one :: b) = mapMaybe (zero ::_) (go zero a b)
  go one (one :: a) [] = yes (zero :: a)
  go one (one :: a) (zero :: b) = mapMaybe (zero ::_) (go zero a b)
  go one (one :: a) (one :: b) = mapMaybe (one ::_) (go one a b)

  _-B_ : BinNat → BinNat → Maybe BinNat
  a -B b = go zero a b

  goEmpty : (a : BinNat) → go zero a [] ≡ yes a
  goEmpty [] = refl
  goEmpty (zero :: a) = refl
  goEmpty (one :: a) = refl

  goOneSelf : (a : BinNat) → go one a a ≡ no
  goOneSelf [] = refl
  goOneSelf (zero :: a) rewrite goOneSelf a = refl
  goOneSelf (one :: a) rewrite goOneSelf a = refl

  goOneEmpty : (b : BinNat) {t : BinNat} → go one [] b ≡ yes t → False
  goOneEmpty [] {t} ()
  goOneEmpty (x :: b) {t} ()

  goOneEmpty' : (b : BinNat) → go one [] b ≡ no
  goOneEmpty' b with inspect (go one [] b)
  goOneEmpty' b | no with≡ x = x
  goOneEmpty' b | yes x₁ with≡ x = exFalso (goOneEmpty b x)

  goZeroEmpty : (b : BinNat) {t : BinNat} → go zero [] b ≡ yes t → canonical b ≡ []
  goZeroEmpty [] {t} = λ _ → refl
  goZeroEmpty (zero :: b) {t} pr with inspect (canonical b)
  goZeroEmpty (zero :: b) {t} pr | [] with≡ pr2 rewrite pr2 = refl
  goZeroEmpty (zero :: b) {t} pr | (x :: r) with≡ pr2 with goZeroEmpty b pr
  ... | u = exFalso (nonEmptyNotEmpty (transitivity (equalityCommutative pr2) u))

  goZeroEmpty' : (b : BinNat) {t : BinNat} → go zero [] b ≡ yes t → canonical t ≡ []
  goZeroEmpty' [] {[]} pr = refl
  goZeroEmpty' (x :: b) {[]} pr = refl
  goZeroEmpty' (zero :: b) {x₁ :: t} pr = goZeroEmpty' b pr

  goZeroIncr : (b : BinNat) → go zero [] (incr b) ≡ no
  goZeroIncr [] = refl
  goZeroIncr (zero :: b) = refl
  goZeroIncr (one :: b) = goZeroIncr b

  goPreservesCanonicalRightEmpty : (b : BinNat) → go zero [] (canonical b) ≡ go zero [] b
  goPreservesCanonicalRightEmpty [] = refl
  goPreservesCanonicalRightEmpty (zero :: b) with inspect (canonical b)
  goPreservesCanonicalRightEmpty (zero :: b) | [] with≡ x with goPreservesCanonicalRightEmpty b
  ... | pr2 rewrite x = pr2
  goPreservesCanonicalRightEmpty (zero :: b) | (x₁ :: y) with≡ x with goPreservesCanonicalRightEmpty b
  ... | pr2 rewrite x = pr2
  goPreservesCanonicalRightEmpty (one :: b) = refl

  goZero : (b : BinNat) {t : BinNat} → mapMaybe canonical (go zero [] b) ≡ yes t → t ≡ []
  goZero b {[]} pr = refl
  goZero b {x :: t} pr with inspect (go zero [] b)
  goZero b {x :: t} pr | no with≡ pr2 rewrite pr2 = exFalso (noNotYes pr)
  goZero b {x :: t} pr | yes x₁ with≡ pr2 with goZeroEmpty b pr2
  ... | u with applyEquality (mapMaybe canonical) (goPreservesCanonicalRightEmpty b)
  ... | bl rewrite u | pr = exFalso (nonEmptyNotEmpty (equalityCommutative (yesInjective bl)))
