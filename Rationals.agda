{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Naturals
open import Integers
open import Groups
open import Rings
open import Fields
open import PrimeNumbers
open import Setoids
open import Functions

module Rationals where
  data Sign : Set where
    Positive : Sign
    Negative : Sign

  record ℚ : Set where
    field
      consNum : ℤ
      consDenom : ℕ
      0<consDenom : 0 <N consDenom
    sign : Sign
    sign with consNum
    sign | nonneg x = Positive
    sign | negSucc x = Negative
    numerator : ℕ
    numerator = {!!}
    denominator : ℕ
    denominator = {!!}
    denomPos : 0 <N denominator
    denomPos = {!!}
    coprime : Coprime numerator denominator
    coprime = {!!}

  multZero : (c : ℤ) → (nonneg 0 *Z c ≡ nonneg 0)
  multZero c with convertZ c
  ... | bl = refl

  zeroMultLemma : {b c : ℤ} → {d : ℕ} → (0 <N d) → (nonneg zero *Z c) ≡ b *Z nonneg d → b ≡ nonneg 0
  zeroMultLemma {nonneg b} {nonneg c} {zero} (le x ()) pr
  zeroMultLemma {nonneg zero} {nonneg c} {succ d} _ pr = refl
  zeroMultLemma {nonneg (succ b)} {nonneg c} {succ d} _ pr rewrite multZero (nonneg c) = naughtE (nonnegInjective pr)
  zeroMultLemma {nonneg zero} {negSucc c} {d} 0<d pr = refl
  zeroMultLemma {nonneg (succ b)} {negSucc c} {zero} (le x ()) pr
  zeroMultLemma {nonneg (succ b)} {negSucc c} {succ d} _ pr rewrite multZero (negSucc c) = naughtE (nonnegInjective pr)
  zeroMultLemma {negSucc b} {c} {zero} ()
  zeroMultLemma {negSucc b} {c} {succ d} _ pr rewrite multZero c = exFalso (done pr)
    where
      done : {a b : ℕ} → nonneg a ≡ negSucc b → False
      done ()

  cancelIntegerMultNegsucc : {a b : ℤ} {c : ℕ} → negSucc c *Z a ≡ negSucc c *Z b → a ≡ b
  cancelIntegerMultNegsucc {nonneg a} {nonneg b} {c} pr = {!!}
  cancelIntegerMultNegsucc {nonneg a} {negSucc b} {c} pr = {!!}
  cancelIntegerMultNegsucc {negSucc a} {b} {c} pr = {!!}

  ℚSetoid : Setoid ℚ
  (ℚSetoid Setoid.∼ record { consNum = numA ; consDenom = denomA ; 0<consDenom = 0<denomA }) record { consNum = numB ; consDenom = denomB ; 0<consDenom = 0<denomB } = numA *Z (nonneg denomB) ≡ numB *Z (nonneg denomA)
  Reflexive.reflexive (Equivalence.reflexive (Setoid.eq ℚSetoid)) = refl
  Symmetric.symmetric (Equivalence.symmetric (Setoid.eq ℚSetoid)) {b} {c} pr = equalityCommutative pr
  Transitive.transitive (Equivalence.transitive (Setoid.eq ℚSetoid)) {record { consNum = a ; consDenom = b ; 0<consDenom = 0<b }} {record { consNum = nonneg zero ; consDenom = d ; 0<consDenom = 0<d }} {record { consNum = e ; consDenom = f ; 0<consDenom = 0<f }} pr1 pr2 = transitivity af=0 (equalityCommutative eb=0)
    where
      e=0 : e ≡ nonneg 0
      e=0 = zeroMultLemma {e} {nonneg f} 0<d pr2
      a=0 : a ≡ nonneg 0
      a=0 = zeroMultLemma {a} {nonneg b} 0<d (equalityCommutative pr1)
      af=0 : a *Z nonneg f ≡ nonneg 0
      af=0 rewrite a=0 = refl
      eb=0 : e *Z nonneg b ≡ nonneg 0
      eb=0 rewrite e=0 = refl
  Transitive.transitive (Equivalence.transitive (Setoid.eq ℚSetoid)) {record { consNum = a ; consDenom = b ; 0<consDenom = 0<b }} {record { consNum = nonneg (succ x) ; consDenom = d ; 0<consDenom = 0<d }} {record { consNum = e ; consDenom = f ; 0<consDenom = 0<f }} pr1 pr2 = {!!}
  Transitive.transitive (Equivalence.transitive (Setoid.eq ℚSetoid)) {record { consNum = a ; consDenom = b ; 0<consDenom = 0<b }} {record { consNum = negSucc x ; consDenom = d ; 0<consDenom = 0<d }} {record { consNum = e ; consDenom = f ; 0<consDenom = 0<f }} pr1 pr2 = {!!}

  _+Q_ : ℚ → ℚ → ℚ
  record { consNum = numA ; consDenom = denomA ; 0<consDenom = prA } +Q record { consNum = numB ; consDenom = denomB ; 0<consDenom = prB } = record { consNum = numA +Z numB ; consDenom = denomA *N denomB ; 0<consDenom = productNonzeroIsNonzero prA prB }

  0Q : ℚ
  0Q = record { consNum = nonneg 0 ; consDenom = 1 ; 0<consDenom = le zero refl }

  negateQ : ℚ → ℚ
  ℚ.consNum (negateQ record { consNum = consNum ; consDenom = consDenom ; 0<consDenom = 0<consDenom }) = Group.inverse (Ring.additiveGroup zRing) consNum
  ℚ.consDenom (negateQ record { consNum = consNum ; consDenom = consDenom ; 0<consDenom = 0<consDenom }) = consDenom
  ℚ.0<consDenom (negateQ record { consNum = consNum ; consDenom = consDenom ; 0<consDenom = 0<consDenom }) = 0<consDenom

  qRightInverse : (a : ℚ) → (a +Q 0Q) ≡ a
  qRightInverse record { consNum = consNum ; consDenom = consDenom ; 0<consDenom = 0<consDenom } = {!!}

  qGroup : Group {_} {ℚ}
  Group.setoid qGroup = ℚSetoid
  Group.wellDefined qGroup pr1 pr2 = {!!}
  Group._·_ qGroup = _+Q_
  Group.identity qGroup = 0Q
  Group.inverse qGroup = negateQ
  Group.multAssoc qGroup = {!!}
  Group.multIdentRight qGroup = {!!}
  Group.multIdentLeft qGroup = {!!}
  Group.invLeft qGroup = {!!}
  Group.invRight qGroup = {!!}

{-
  data Sign : Set where
    Positive : Sign
    Negative : Sign

  record Absℚ : Set where
    field
      numerator : ℕ
      denominator : ℕ
      denomPos : 0 <N denominator
      hcf : hcfData denominator numerator
      coprime : 0 <N hcfData.c hcf

  data ℚ : Set where
    0Q : ℚ
    positiveQ : Absℚ → ℚ
    negativeQ : Absℚ → ℚ

  equalityAbsQ : (a : Absℚ) → (b : Absℚ) → (numsEq : Absℚ.numerator a ≡ Absℚ.numerator b) → (denomsEq : Absℚ.denominator a ≡ Absℚ.denominator b) → a ≡ b
  equalityAbsQ record { numerator = numeratorA ; denominator = denominatorA ; denomPos = denomPosA ; hcf = hcfA ; coprime = coprimeA } record { numerator = .numeratorA ; denominator = .denominatorA ; denomPos = denomPos ; hcf = hcf ; coprime = coprime } refl refl rewrite <NRefl denomPosA denomPos = {!!}

  injectℤ : (a : ℤ) → ℚ
  injectℤ (nonneg zero) = 0Q
  injectℤ (nonneg (succ x)) = positiveQ record { numerator = x ; denominator = 1 ; denomPos = le zero refl ; hcf = record { c = 1 ; c|a = aDivA 1 ; c|b = oneDivN x ; hcf = λ i i|1 i|x → i|1 } ; coprime = le zero refl }
    where
      q : 1 ≡ x *N 0 +N 1
      q rewrite multiplicationNIsCommutative x 0 = refl
  injectℤ (negSucc x) = negativeQ record { numerator = succ x ; denominator = 1 ; denomPos = le zero refl ; hcf = record { c = 1 ; c|a = aDivA 1 ; c|b = oneDivN (succ x) ; hcf = λ i i|1 i|x → i|1 } ; coprime = le zero refl }
    where
      q : 1 ≡ x *N 0 +N 1
      q rewrite multiplicationNIsCommutative x 0 = refl

  cancel : (numerator denominator : ℕ) → (0 <N denominator) → Absℚ
  cancel num zero ()
  cancel num (succ denom) _ with euclid num (succ denom)
  cancel num (succ denom) _ | record { hcf = record { c = c ; c|a = divides record { quot = num/c ; rem = .0 ; pr = c*num/c ; remIsSmall = 0<c } refl ; c|b = divides record { quot = sd/c ; rem = .0 ; pr = c*d/c ; remIsSmall = 0<c' } refl ; hcf = hcf } } = record { numerator = num/c ; denominator = sd/c ; denomPos = 0<sd/c sd/c c*d/c ; hcf = h ; coprime = le zero refl }
    where
      lemm : {b c : ℕ} → (c ≡ 0) → (c *N b ≡ 0)
      lemm {b} {c} c=0 rewrite c=0 = refl
      cNonzero : (c ≡ 0) → False
      cNonzero c=0 = naughtE (identityOfIndiscernablesLeft _ _ _ _≡_ c*d/c (applyEquality (_+N 0) (lemm c=0)))
      0<sd/c : (sd/c : ℕ) → (c *N sd/c +N 0 ≡ succ denom) → 0 <N sd/c
      0<sd/c zero pr rewrite multiplicationNIsCommutative c zero = naughtE pr
      0<sd/c (succ sd/c) pr = succIsPositive _
      h : hcfData sd/c num/c
      h = record
            { c = 1
            ; c|a = oneDivN _
            ; c|b = oneDivN _
            ; hcf = {!!}
            }

  productPos : {denomA denomB : ℕ} → (0 <N denomA) → (0 <N denomB) → 0 <N denomA *N denomB
  productPos {zero} {b} ()
  productPos {succ a} {zero} 0<a ()
  productPos {succ a} {succ b} _ _ = succIsPositive _

  addToPositive : (p : Absℚ) → ℚ → ℚ
  addToPositive p 0Q = positiveQ p
  addToPositive (record { numerator = numA ; denominator = denomA ; denomPos = denomAPos ; hcf = hcfA ; coprime = coprimeA }) (positiveQ record { numerator = numB ; denominator = denomB ; denomPos = denomBPos ; hcf = hcfB ; coprime = coprimeB }) = positiveQ (cancel (numA *N denomB +N numB *N denomA) (denomA *N denomB) (productPos denomAPos denomBPos))
  addToPositive (record { numerator = numA ; denominator = denomA ; denomPos = denomAPos ; hcf = hcfA ; coprime = coprimeA }) (negativeQ record { numerator = numB ; denominator = denomB ; denomPos = denomBPos ; hcf = hcfB ; coprime = coprimeB }) with orderIsTotal (numA *N denomB) (numB *N denomA)
  ... | inl (inl (le x pr)) = negativeQ (cancel x (denomA *N denomB) (productPos denomAPos denomBPos))
  ... | inl (inr (le x pr)) = positiveQ (cancel x (denomA *N denomB) (productPos denomAPos denomBPos))
  ... | inr x = 0Q

  infix 15 _+Q_
  _+Q_ : ℚ → ℚ → ℚ
  0Q +Q b = b
  positiveQ x +Q b = addToPositive x b
  negativeQ a +Q 0Q = negativeQ a
  negativeQ a +Q positiveQ x = addToPositive x (negativeQ a)
  negativeQ record { numerator = numA ; denominator = denomA ; denomPos = denomAPos ; hcf = hcfA ; coprime = coprimeA } +Q negativeQ record { numerator = numB ; denominator = denomB ; denomPos = denomBPos ; hcf = hcfB ; coprime = coprimeB } = negativeQ (cancel (numA *N denomB +N numB *N denomA) (denomA *N denomB) (productPos denomAPos denomBPos))

  negateQ : ℚ → ℚ
  negateQ 0Q = 0Q
  negateQ (positiveQ x) = negativeQ x
  negateQ (negativeQ x) = positiveQ x

  negatePlusLeft : (a : ℚ) → ((negateQ a) +Q a ≡ 0Q)
  negatePlusLeft 0Q = refl
  negatePlusLeft (positiveQ x) = {!!}
  negatePlusLeft (negativeQ x) = {!!}

-}

{-
  infix 25 _*Q_
  _*Q_ : ℚ → ℚ → ℚ
  record { numerator = numA ; denominator = zero ; denomPos = le x () } *Q b
  record { numerator = numA ; denominator = succ denomA ; denomPos = denomPosA } *Q record { numerator = numB ; denominator = 0 ; denomPos = () }
  record { sign = Positive ; numerator = numA ; denominator = succ denomA ; denomPos = denomPosA ; division = divisionA ; coprime = coprimeA } *Q record { sign = Positive ; numerator = numB ; denominator = succ denomB ; denomPos = denomPosB ; division = divisionB ; coprime = coprimeB } = record { sign = Positive ; numerator = {!!} ; denominator = {!!} ; denomPos = {!!} ; division = {!!} ; coprime = {!!} }
  record { sign = Positive ; numerator = numA ; denominator = succ denomA ; denomPos = denomPosA ; division = divisionA ; coprime = coprimeA } *Q record { sign = Negative ; numerator = numB ; denominator = succ denomB ; denomPos = denomPosB ; division = divisionB ; coprime = coprimeB } = {!!}
  record { sign = Negative ; numerator = numA ; denominator = succ denomA ; denomPos = denomPosA ; division = divisionA ; coprime = coprimeA } *Q record { sign = sgnB ; numerator = numB ; denominator = succ denomB ; denomPos = denomPosB ; division = divisionB ; coprime = coprimeB } = {!!}
  -}
