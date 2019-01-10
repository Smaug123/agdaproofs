{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals
open import Groups.Groups
open import Rings.RingDefinition
open import Functions
open import Orders
open import Setoids.Setoids
open import Setoids.Orders
open import Rings.IntegralDomains

module Numbers.Integers where
    data ℤ : Set where
      nonneg : ℕ → ℤ
      negSucc : ℕ → ℤ

    data ℤSimple : Set where
      negative : (a : ℕ) → (0 <N a) → ℤSimple
      positive : (a : ℕ) → (0 <N a) → ℤSimple
      zZero : ℤSimple

    convertZ : ℤ → ℤSimple
    convertZ (nonneg zero) = zZero
    convertZ (nonneg (succ x)) = positive (succ x) (succIsPositive x)
    convertZ (negSucc x) = negative (succ x) (succIsPositive x)

    convertZ' : ℤSimple → ℤ
    convertZ' (negative zero (le x ()))
    convertZ' (negative (succ a) x) = negSucc a
    convertZ' (positive a x) = nonneg a
    convertZ' zZero = nonneg zero

    zIsZ : (a : ℤ) → convertZ' (convertZ a) ≡ a
    zIsZ (nonneg zero) = refl
    zIsZ (nonneg (succ x)) = refl
    zIsZ (negSucc x) = refl

    zIsZ' : (a : ℤSimple) → convertZ (convertZ' a) ≡ a
    zIsZ' (negative zero (le x ()))
    zIsZ' (negative (succ a) x) = help
      where
        eq : (succIsPositive a) ≡ x
        eq = <NRefl {0} {succ a} (succIsPositive a) x
        help : negative (succ a) (succIsPositive a) ≡ negative (succ a) x
        help rewrite eq = refl
    zIsZ' (positive zero (le x ()))
    zIsZ' (positive (succ a) x) = help
      where
        eq : (succIsPositive a) ≡ x
        eq = <NRefl {0} {succ a} (succIsPositive a) x
        help : positive (succ a) (succIsPositive a) ≡ positive (succ a) x
        help rewrite eq = refl
    zIsZ' zZero = refl

    posIsPos : {a : ℕ} → (pr1 pr2 : 0 <N a) → (positive a pr1 ≡ positive a pr2)
    posIsPos {a} pr1 pr2 rewrite <NRefl pr1 pr2 = refl

    negIsNeg : {a : ℕ} → (pr1 pr2 : 0 <N a) → (negative a pr1 ≡ negative a pr2)
    negIsNeg {a} pr1 pr2 rewrite <NRefl pr1 pr2 = refl

    infix 15 _+Z_
    _+Z_ : ℤ → ℤ → ℤ
    nonneg zero +Z r = r
    nonneg (succ x) +Z nonneg y = nonneg (succ x +N y)
    nonneg (succ x) +Z negSucc zero = nonneg x
    nonneg (succ x) +Z negSucc (succ a) = nonneg x +Z negSucc a
    negSucc a +Z nonneg zero = negSucc a
    negSucc zero +Z nonneg (succ x) = nonneg x
    negSucc (succ a) +Z nonneg (succ x) = negSucc a +Z nonneg x
    negSucc zero +Z negSucc b = negSucc (succ b)
    negSucc (succ a) +Z negSucc b = negSucc (succ a +N succ b)

    depth : ℤSimple → ℕ
    depth (negative a x) = a
    depth (positive a x) = a
    depth zZero = 0

    plusZ' : (height : ℕ) → (a : ℤSimple) → (b : ℤSimple) → (depth a +N depth b ≡ height) → ℤSimple
    plusZ' zero (negative zero (le x ())) (negative a₁ x₁) pr
    plusZ' zero (negative (succ a) (le x proof)) (negative a₁ x₁) pr = naughtE (equalityCommutative pr)
    plusZ' zero (negative zero (le x ())) (positive a₁ x₁) pr
    plusZ' zero (negative (succ a) (le x proof)) (positive a₁ x₁) pr = naughtE (equalityCommutative pr)
    plusZ' zero (negative zero (le x ())) zZero pr
    plusZ' zero (negative (succ a) (le x proof)) zZero pr = naughtE (equalityCommutative pr)
    plusZ' zero (positive zero (le x ())) b pr
    plusZ' zero (positive (succ a) x) b pr = naughtE (equalityCommutative pr)
    plusZ' zero zZero (negative zero (le x ())) pr
    plusZ' zero zZero (negative (succ a) x) pr = naughtE (equalityCommutative pr)
    plusZ' zero zZero (positive zero (le x ())) pr
    plusZ' zero zZero (positive (succ a) x) pr = naughtE (equalityCommutative pr)
    plusZ' zero zZero zZero pr = zZero
    plusZ' (succ height) (negative zero (le x ())) b pr
    plusZ' (succ height) (negative (succ a) _) (negative zero (le x ())) pr
    plusZ' (succ height) (negative (succ a) _) (negative (succ b) _) pr = negative (succ a +N succ b) (succIsPositive _)
    plusZ' (succ height) (negative (succ a) _) (positive zero (le x ())) pr
    plusZ' (succ height) (negative (succ zero) _) (positive (succ zero) _) pr = zZero
    plusZ' (succ height) (negative (succ zero) _) (positive (succ (succ b)) _) pr = positive (succ b) (succIsPositive b)
    plusZ' (succ height) (negative (succ (succ a)) _) (positive (succ zero) x) pr = negative (succ a) (succIsPositive a)
    plusZ' (succ zero) (negative (succ (succ a)) _) (positive (succ (succ b)) x) pr = naughtE (equalityCommutative (succInjective pr))
    plusZ' (succ (succ height)) (negative (succ (succ a)) _) (positive (succ (succ b)) x) pr = plusZ' height (negative (succ a) (succIsPositive _)) (positive (succ b) (succIsPositive _)) ans
      where
        h : a +N succ (succ b) ≡ height
        h = succInjective (succInjective pr)
        ans : succ (a +N succ b) ≡ height
        ans rewrite additionNIsCommutative a (succ b) | additionNIsCommutative (succ (succ b)) a = h
    plusZ' (succ height) (negative (succ a) _) zZero pr = negative (succ a) (succIsPositive a)
    plusZ' (succ height) (positive zero (le x ())) b pr
    plusZ' (succ height) (positive (succ a) _) (negative zero (le x ())) pr
    plusZ' (succ height) (positive (succ zero) _) (negative (succ zero) _) pr = zZero
    plusZ' (succ height) (positive (succ zero) _) (negative (succ (succ b)) _) pr = negative (succ b) (succIsPositive b)
    plusZ' (succ height) (positive (succ (succ a)) _) (negative (succ zero) _) pr = positive (succ a) (succIsPositive a)
    plusZ' (succ zero) (positive (succ (succ a)) _) (negative (succ (succ b)) _) pr = naughtE (equalityCommutative (succInjective pr))
    plusZ' (succ (succ height)) (positive (succ (succ a)) _) (negative (succ (succ b)) _) pr = plusZ' height (positive (succ a) (succIsPositive a)) (negative (succ b) (succIsPositive b)) ans
      where
        h : a +N succ (succ b) ≡ height
        h = succInjective (succInjective pr)
        ans : succ (a +N succ b) ≡ height
        ans rewrite additionNIsCommutative a (succ b) | additionNIsCommutative (succ (succ b)) a = h
    plusZ' (succ height) (positive (succ a) _) (positive b x) pr = positive (succ a +N b) (succIsPositive (a +N b))
    plusZ' (succ height) (positive (succ a) _) zZero pr = positive (succ a) (succIsPositive a)
    plusZ' (succ height) zZero b pr = b

    infix 15 _+Z'_
    _+Z'_ : ℤSimple → ℤSimple → ℤSimple
    a +Z' b = plusZ' (depth a +N depth b) a b refl

    castPlusZ' : {de1 de2 : ℕ} → (r s : ℤSimple) → {pr : depth r +N depth s ≡ de1} → {pr2 : depth r +N depth s ≡ de2} → de1 ≡ de2 → plusZ' de1 r s pr ≡ plusZ' de2 r s pr2
    castPlusZ' {.(depth r +N depth s)} {.(depth r +N depth s)} (r) (s) {refl} {refl} de1=de2 = refl

    canKnockOneOff+Z'' : (a b : ℕ) → {pr1 : 0 <N a} → {pr2 : 0 <N b} → {pr3 : 0 <N succ a} → {pr4 : 0 <N succ b} → plusZ' (succ a +N succ b) (positive (succ a) pr3) (negative (succ b) pr4) refl ≡ (plusZ' (a +N b) (positive a pr1) (negative b pr2) refl)
    canKnockOneOff+Z'' zero b {le x ()} {pr2}
    canKnockOneOff+Z'' (succ a) zero {pr1} {le x ()}
    canKnockOneOff+Z'' (succ a) (succ b) {pr1} {pr2} {pr3} {pr4} rewrite <NRefl (succIsPositive a) pr1 | <NRefl (succIsPositive b) pr2 = castPlusZ' {a +N succ (succ b)} {succ (a +N succ b)} (positive (succ a) pr1) (negative (succ b) pr2) help
      where
        help : a +N (succ (succ b)) ≡ succ (a +N succ b)
        help rewrite additionNIsCommutative a (succ (succ b)) | additionNIsCommutative (succ b) a = refl

    canKnockOneOff+Z''2 : (a b : ℕ) → {pr1 : 0 <N a} → {pr2 : 0 <N b} → {pr3 : 0 <N succ a} → {pr4 : 0 <N succ b} → plusZ' (succ a +N succ b) (negative (succ a) pr3) (positive (succ b) pr4) refl ≡ (plusZ' (a +N b) (negative a pr1) (positive b pr2) refl)
    canKnockOneOff+Z''2 zero b {le x ()} {pr2}
    canKnockOneOff+Z''2 (succ a) zero {pr1} {le x ()}
    canKnockOneOff+Z''2 (succ a) (succ b) {pr1} {pr2} {pr3} {pr4} rewrite <NRefl (succIsPositive a) pr1 | <NRefl (succIsPositive b) pr2 = castPlusZ' {a +N succ (succ b)} {succ (a +N succ b)} (negative (succ a) pr1) (positive (succ b) pr2) help
      where
        help : a +N (succ (succ b)) ≡ succ (a +N succ b)
        help rewrite additionNIsCommutative a (succ (succ b)) | additionNIsCommutative (succ b) a = refl

    lemma' : (x y : ℕ) → succ (x +N succ y) ≡ x +N succ (succ y)
    lemma' x y = equalityCommutative (succExtracts x (succ y))

    helpPlusIsPlus' : (x y : ℕ) → (pr' : _) → negative (succ x) (succIsPositive x) +Z' positive (succ y) (succIsPositive y) ≡ plusZ' (x +N succ (succ y)) (negative (succ x) (logical<NImpliesLe (record {}))) (positive (succ y) (logical<NImpliesLe (record {}))) pr'
    helpPlusIsPlus' x y pr = castPlusZ' {succ x +N succ y} {x +N succ (succ y)} (negative (succ x) (succIsPositive x)) (positive (succ y) (succIsPositive y)) {refl} {pr} pr

    helpPlusIsPlus'2 : (x y : ℕ) → (pr' : _) → positive (succ x) (succIsPositive x) +Z' negative (succ y) (succIsPositive y) ≡ plusZ' (succ (x +N succ y)) (positive (succ x) (logical<NImpliesLe (record {}))) (negative (succ y) (logical<NImpliesLe (record {}))) pr'
    helpPlusIsPlus'2 x y pr = castPlusZ' {_} {_} (positive (succ x) (succIsPositive x)) (negative (succ y) (succIsPositive y)) {refl} {pr} pr

    canKnockOneOff+Z' : (a b : ℕ) → {pr1 : 0 <N a} → {pr2 : 0 <N b} → {pr3 : 0 <N succ a} → {pr4 : 0 <N succ b} → (positive (succ a) pr3) +Z' (negative (succ b) pr4) ≡ (positive a pr1) +Z' (negative b pr2)
    canKnockOneOff+Z' zero b {le x ()} {pr2} {pr3} {pr4}
    canKnockOneOff+Z' (succ a) zero {pr1} {le x ()} {pr3} {pr4}
    canKnockOneOff+Z' (succ a) (succ b) {pr1} {pr2} {pr3} {pr4} = canKnockOneOff+Z'' (succ a) (succ b) {pr1} {pr2} {pr3} {pr4}

    canKnockOneOff+Z'2 : (a b : ℕ) → {pr1 : 0 <N a} → {pr2 : 0 <N b} → {pr3 : 0 <N succ a} → {pr4 : 0 <N succ b} → (negative (succ a) pr3) +Z' (positive (succ b) pr4) ≡ (negative a pr1) +Z' (positive b pr2)
    canKnockOneOff+Z'2 zero b {le x ()} {pr2} {pr3} {pr4}
    canKnockOneOff+Z'2 (succ a) zero {pr1} {le x ()} {pr3} {pr4}
    canKnockOneOff+Z'2 (succ a) (succ b) {pr1} {pr2} {pr3} {pr4} = canKnockOneOff+Z''2 (succ a) (succ b) {pr1} {pr2} {pr3} {pr4}

    plusIsPlus' : (a b : ℤ) → convertZ (a +Z b) ≡ (convertZ a) +Z' (convertZ b)
    plusIsPlus' (nonneg zero) (nonneg zero) = refl
    plusIsPlus' (nonneg zero) (nonneg (succ x)) = refl
    plusIsPlus' (nonneg zero) (negSucc x) = refl
    plusIsPlus' (nonneg (succ x)) (nonneg zero) rewrite additionNIsCommutative x 0 = refl
    plusIsPlus' (nonneg (succ x)) (nonneg (succ y)) = refl
    plusIsPlus' (nonneg (succ zero)) (negSucc zero) = refl
    plusIsPlus' (nonneg (succ (succ x))) (negSucc zero) = refl
    plusIsPlus' (nonneg (succ zero)) (negSucc (succ y)) = refl
    plusIsPlus' (nonneg (succ (succ x))) (negSucc (succ y)) rewrite canKnockOneOff+Z' (succ x) (succ y) {succIsPositive x} {succIsPositive y} {succIsPositive (succ x)} {succIsPositive (succ y)} = identityOfIndiscernablesRight _ _ _ _≡_ (plusIsPlus' (nonneg (succ x)) (negSucc y)) (helpPlusIsPlus'2 x y _)
    plusIsPlus' (negSucc x) (nonneg zero) = refl
    plusIsPlus' (negSucc zero) (nonneg (succ zero)) = refl
    plusIsPlus' (negSucc zero) (nonneg (succ (succ y))) = refl
    plusIsPlus' (negSucc (succ x)) (nonneg (succ zero)) = refl
    plusIsPlus' (negSucc (succ x)) (nonneg (succ (succ y))) rewrite equalityCommutative (canKnockOneOff+Z' (succ x) (succ y) {succIsPositive x} {succIsPositive y} {succIsPositive (succ x)} {succIsPositive (succ y)}) = identityOfIndiscernablesRight (convertZ (negSucc x +Z nonneg (succ y))) (negative (succ x) (succIsPositive x) +Z' positive (succ y) (succIsPositive y)) _ _≡_ (plusIsPlus' (negSucc x) (nonneg (succ y))) (helpPlusIsPlus' x y _)
    plusIsPlus' (negSucc zero) (negSucc zero) = refl
    plusIsPlus' (negSucc zero) (negSucc (succ y)) = refl
    plusIsPlus' (negSucc (succ x)) (negSucc y) = refl

    plusIsPlusFirstPos : (a : ℕ) (pr1 : 0 <N a) → (b : ℤSimple) → convertZ' ((positive a pr1) +Z' b) ≡ (convertZ' (positive a pr1)) +Z (convertZ' b)
    plusIsPlusFirstPos zero (le x ()) b
    plusIsPlusFirstPos (succ zero) pr1 (negative zero (le x ()))
    plusIsPlusFirstPos (succ zero) pr1 (negative (succ zero) x) = refl
    plusIsPlusFirstPos (succ zero) pr1 (negative (succ (succ b)) x) = refl
    plusIsPlusFirstPos (succ zero) pr1 (positive b x) = refl
    plusIsPlusFirstPos (succ zero) pr1 zZero = refl
    plusIsPlusFirstPos (succ (succ a)) pr1 (negative zero (le x ()))
    plusIsPlusFirstPos (succ (succ a)) pr1 (negative (succ zero) x) = refl
    plusIsPlusFirstPos (succ (succ a)) pr1 (negative (succ (succ b)) x) rewrite canKnockOneOff+Z' (succ a) (succ b) {succIsPositive a} {succIsPositive b} {pr1} {x} = plusIsPlusFirstPos (succ a) (logical<NImpliesLe (record {})) (negative (succ b) (logical<NImpliesLe (record {})))
    plusIsPlusFirstPos (succ (succ a)) pr1 (positive zero (le x ()))
    plusIsPlusFirstPos (succ (succ a)) pr1 (positive (succ zero) x) = refl
    plusIsPlusFirstPos (succ (succ a)) pr1 (positive (succ (succ b)) x) = refl
    plusIsPlusFirstPos (succ (succ a)) pr1 zZero rewrite additionNIsCommutative a 0 = refl

    plusIsPlusFirstNeg : (a : ℕ) (pr1 : 0 <N a) → (b : ℤSimple) → convertZ' ((negative a pr1) +Z' b) ≡ (convertZ' (negative a pr1)) +Z (convertZ' b)
    plusIsPlusFirstNeg zero (le x ()) b
    plusIsPlusFirstNeg (succ zero) pr (negative zero (le x ()))
    plusIsPlusFirstNeg (succ zero) pr (negative (succ a) x) = refl
    plusIsPlusFirstNeg (succ zero) pr (positive zero (le x ()))
    plusIsPlusFirstNeg (succ zero) pr (positive (succ zero) x) = refl
    plusIsPlusFirstNeg (succ zero) pr (positive (succ (succ a)) x) = refl
    plusIsPlusFirstNeg (succ zero) pr zZero = refl
    plusIsPlusFirstNeg (succ (succ a)) pr (negative zero (le x ()))
    plusIsPlusFirstNeg (succ (succ a)) pr (negative (succ b) x) = refl
    plusIsPlusFirstNeg (succ (succ a)) pr (positive zero (le x ()))
    plusIsPlusFirstNeg (succ (succ a)) pr (positive (succ zero) x) = refl
    plusIsPlusFirstNeg (succ (succ a)) pr (positive (succ (succ b)) x) rewrite canKnockOneOff+Z'2 (succ a) (succ b) {succIsPositive a} {succIsPositive b} {pr} {x} = plusIsPlusFirstNeg (succ a) (logical<NImpliesLe (record {})) (positive (succ b) (logical<NImpliesLe (record {})))
    plusIsPlusFirstNeg (succ (succ a)) pr zZero = refl

    plusIsPlus : (a b : ℤSimple) → convertZ' (a +Z' b) ≡ (convertZ' a) +Z (convertZ' b)
    plusIsPlus (negative a pr) b = plusIsPlusFirstNeg a pr b
    plusIsPlus (positive a pr) b = plusIsPlusFirstPos a pr b
    plusIsPlus zZero (negative zero (le x ()))
    plusIsPlus zZero (negative (succ a) x) = refl
    plusIsPlus zZero (positive zero (le x ()))
    plusIsPlus zZero (positive (succ a) x) = refl
    plusIsPlus zZero zZero = refl

    infix 25 _*Z'_
    _*Z'_ : ℤSimple → ℤSimple → ℤSimple
    negative zero (le x ()) *Z' b
    negative (succ a) x *Z' negative zero (le x₁ ())
    negative (succ a) x *Z' negative (succ b) prb = positive (succ a *N succ b) (succIsPositive (b +N a *N succ b))
    negative (succ a) x *Z' positive zero (le x₁ ())
    negative (succ a) x *Z' positive (succ b) prb = negative (succ a *N succ b) (succIsPositive (b +N a *N succ b))
    negative (succ a) x *Z' zZero = zZero
    positive zero (le x ()) *Z' b
    positive (succ a) x *Z' negative zero (le x₁ ())
    positive (succ a) x *Z' negative (succ b) prb = negative (succ a *N succ b) (succIsPositive (b +N a *N succ b))
    positive (succ a) x *Z' positive zero (le x₁ ())
    positive (succ a) x *Z' positive (succ b) prb = positive (succ a *N succ b) (succIsPositive (b +N a *N succ b))
    positive (succ a) x *Z' zZero = zZero
    zZero *Z' b = zZero

    infix 25 _*Z_
    _*Z_ : ℤ → ℤ → ℤ
    a *Z b = convertZ' (convertZ a *Z' convertZ b)

    convertZ'DistributesOver*Z : (a b : ℤSimple) → convertZ' (a *Z' b) ≡ (convertZ' a) *Z (convertZ' b)
    convertZ'DistributesOver*Z (negative zero (le x ())) (negative b prb)
    convertZ'DistributesOver*Z (negative (succ a) x) (negative zero (le y ()))
    convertZ'DistributesOver*Z (negative (succ a) x) (negative (succ b) prb) = refl
    convertZ'DistributesOver*Z (negative zero (le x ())) (positive b prb)
    convertZ'DistributesOver*Z (negative (succ a) x) (positive zero (le x₁ ()))
    convertZ'DistributesOver*Z (negative (succ a) x) (positive (succ b) prb) = refl
    convertZ'DistributesOver*Z (negative zero (le x ())) zZero
    convertZ'DistributesOver*Z (negative (succ a) x) zZero = refl
    convertZ'DistributesOver*Z (positive zero (le x ())) b
    convertZ'DistributesOver*Z (positive (succ a) x) (negative zero (le x₁ ()))
    convertZ'DistributesOver*Z (positive (succ a) x) (negative (succ b) prb) = refl
    convertZ'DistributesOver*Z (positive (succ a) x) (positive zero (le x₁ ()))
    convertZ'DistributesOver*Z (positive (succ a) x) (positive (succ b) prb) = refl
    convertZ'DistributesOver*Z (positive (succ a) x) zZero = refl
    convertZ'DistributesOver*Z zZero (negative zero (le x ()))
    convertZ'DistributesOver*Z zZero (negative (succ a) x) = refl
    convertZ'DistributesOver*Z zZero (positive zero (le x ()))
    convertZ'DistributesOver*Z zZero (positive (succ a) x) = refl
    convertZ'DistributesOver*Z zZero zZero = refl

    infix 5 _<Z_
    record _<Z_ (a : ℤ) (b : ℤ) : Set where
      constructor le
      field
          x : ℕ
          proof : (nonneg (succ x)) +Z a ≡ b

    addingNonnegIsHom : (a b : ℕ) → nonneg a +Z nonneg b ≡ nonneg (a +N b)
    addingNonnegIsHom zero b = refl
    addingNonnegIsHom (succ a) b = refl

    multiplyingNonnegIsHom : (a b : ℕ) → nonneg a *Z nonneg b ≡ nonneg (a *N b)
    multiplyingNonnegIsHom zero b = refl
    multiplyingNonnegIsHom (succ a) zero rewrite multiplicationNIsCommutative a 0 = refl
    multiplyingNonnegIsHom (succ a) (succ b) = refl

    multiplyWithZero : (a : ℤ) → a *Z nonneg 0 ≡ nonneg 0
    multiplyWithZero (nonneg zero) rewrite multiplyingNonnegIsHom zero zero = refl
    multiplyWithZero (nonneg (succ x)) rewrite multiplyingNonnegIsHom (succ x) zero = refl
    multiplyWithZero (negSucc x) = refl

    multiplyWithZero' : (a : ℤ) → nonneg 0 *Z a ≡ nonneg 0
    multiplyWithZero' (nonneg x) = refl
    multiplyWithZero' (negSucc zero) = refl
    multiplyWithZero' (negSucc (succ x)) = refl

    nonnegInjective : {a b : ℕ} → (nonneg a ≡ nonneg b) → (a ≡ b)
    nonnegInjective {a} {.a} refl = refl

    lessIsPreservedNToZ : {a b : ℕ} → (a <N b) → ((nonneg a) <Z (nonneg b))
    _<Z_.x (lessIsPreservedNToZ {a} {b} (le x proof)) = x
    _<Z_.proof (lessIsPreservedNToZ {a} {.(succ (x +N a))} (le x refl)) = refl

    lessIsPreservedNToZConverse : {a b : ℕ} → ((nonneg a) <Z (nonneg b)) → (a <N b)
    lessIsPreservedNToZConverse {a} {b} (le x proof) = le x (nonnegInjective proof)

    additionZIsCommutative : (a b : ℤ) → a +Z b ≡ b +Z a
    additionZIsCommutative (nonneg x) (nonneg y) = splitRight
      where
        inN : x +N y ≡ y +N x
        inN = additionNIsCommutative x y
        inZ : nonneg (x +N y) ≡ nonneg (y +N x)
        inZ = applyEquality nonneg inN
        splitLeft : nonneg x +Z nonneg y ≡ nonneg (y +N x)
        splitLeft = identityOfIndiscernablesLeft (nonneg (x +N y)) (nonneg (y +N x)) (nonneg x +Z nonneg y) _≡_ inZ (equalityCommutative (addingNonnegIsHom x y))
        splitRight : nonneg x +Z nonneg y ≡ nonneg y +Z nonneg x
        splitRight = identityOfIndiscernablesRight (nonneg x +Z nonneg y) (nonneg (y +N x)) (nonneg y +Z nonneg x) _≡_ splitLeft (equalityCommutative (addingNonnegIsHom y x))

    additionZIsCommutative (nonneg zero) (negSucc a) = refl
    additionZIsCommutative (nonneg (succ x)) (negSucc zero) = refl
    additionZIsCommutative (nonneg (succ x)) (negSucc (succ a)) = additionZIsCommutative (nonneg x) (negSucc a)
    additionZIsCommutative (negSucc zero) (nonneg zero) = refl
    additionZIsCommutative (negSucc (succ a)) (nonneg zero) = refl
    additionZIsCommutative (negSucc zero) (nonneg (succ x)) = refl
    additionZIsCommutative (negSucc (succ a)) (nonneg (succ x)) = additionZIsCommutative (negSucc a) (nonneg x)
    additionZIsCommutative (negSucc zero) (negSucc zero) = refl
    additionZIsCommutative (negSucc zero) (negSucc (succ b)) = applyEquality negSucc i
      where
        h : succ b ≡ b +N succ zero
        h = succIsAddOne b
        i : succ (succ b) ≡ succ (b +N succ zero)
        i = applyEquality succ h

    additionZIsCommutative (negSucc (succ a)) (negSucc zero) = applyEquality negSucc i
      where
        i : succ (a +N succ zero) ≡ succ (succ a)
        i = applyEquality succ (equalityCommutative (succIsAddOne a))

    additionZIsCommutative (negSucc (succ a)) (negSucc (succ b)) = applyEquality negSucc (applyEquality succ j)
      where
        m : succ (a +N b) ≡ succ (b +N a)
        m = applyEquality succ (additionNIsCommutative a b)
        r : a +N succ b ≡ b +N succ a
        r = transitivity (succExtracts a b) (transitivity m (equalityCommutative (succExtracts b a)))
        k : succ (a +N succ b) ≡ succ (b +N succ a)
        k rewrite additionNIsCommutative a (succ b) | additionNIsCommutative b a | additionNIsCommutative (succ a) b = refl
        j : a +N succ (succ b) ≡ b +N succ (succ a)
        j = transitivity (succExtracts a (succ b)) (transitivity k (equalityCommutative (succExtracts b (succ a))))

    additiveInverseExists : (a : ℕ) → (negSucc a +Z nonneg (succ a)) ≡ nonneg 0
    additiveInverseExists zero = refl
    additiveInverseExists (succ a) = additiveInverseExists a

    multiplicationZ'IsCommutative : (a b : ℤSimple) → (a *Z' b ≡ b *Z' a)
    multiplicationZ'IsCommutative (negative zero (le x ())) (negative b prb)
    multiplicationZ'IsCommutative (negative (succ a) _) (negative zero (le x ()))
    multiplicationZ'IsCommutative (negative (succ a) x) (negative (succ b) prb) = res (succIsPositive (b +N a *N succ b)) (succIsPositive (a +N b *N succ a))
      where
        h : succ a *N succ b ≡ succ b *N succ a
        h = multiplicationNIsCommutative (succ a) (succ b)
        res : (pr1 : 0 <N succ b +N a *N succ b) → (pr2 : 0 <N succ a +N b *N succ a) → positive (succ a *N succ b) pr1 ≡ positive (succ b *N succ a) pr2
        res pr1 pr2 rewrite h = posIsPos pr1 pr2
    multiplicationZ'IsCommutative (negative zero (le x ())) (positive b prb)
    multiplicationZ'IsCommutative (negative (succ a) x) (positive zero (le _ ()))
    multiplicationZ'IsCommutative (negative (succ a) x) (positive (succ b) prb) = res (succIsPositive (b +N a *N succ b)) (succIsPositive (a +N b *N succ a))
      where
        h : succ a *N succ b ≡ succ b *N succ a
        h = multiplicationNIsCommutative (succ a) (succ b)
        res : (pr1 : 0 <N succ b +N a *N succ b) → (pr2 : 0 <N succ a +N b *N succ a) → negative (succ a *N succ b) pr1 ≡ negative (succ b *N succ a) pr2
        res pr1 pr2 rewrite h = negIsNeg pr1 pr2
    multiplicationZ'IsCommutative (negative zero (le x ())) zZero
    multiplicationZ'IsCommutative (negative (succ a) x) zZero = refl
    multiplicationZ'IsCommutative (positive zero (le x ())) (negative b prb)
    multiplicationZ'IsCommutative (positive (succ a) x) (negative zero (le _ ()))
    multiplicationZ'IsCommutative (positive (succ a) x) (negative (succ b) prb) = res (succIsPositive (b +N a *N succ b)) (succIsPositive (a +N b *N succ a))
      where
        h : succ a *N succ b ≡ succ b *N succ a
        h = multiplicationNIsCommutative (succ a) (succ b)
        res : (pr1 : 0 <N succ b +N a *N succ b) → (pr2 : 0 <N succ a +N b *N succ a) → negative (succ a *N succ b) pr1 ≡ negative (succ b *N succ a) pr2
        res pr1 pr2 rewrite h = negIsNeg pr1 pr2
    multiplicationZ'IsCommutative (positive zero (le x ())) (positive b prb)
    multiplicationZ'IsCommutative (positive (succ a) x) (positive zero (le x₁ ()))
    multiplicationZ'IsCommutative (positive (succ a) _) (positive (succ b) _) = res (succIsPositive (b +N a *N succ b)) (succIsPositive (a +N b *N succ a))
      where
        h : succ a *N succ b ≡ succ b *N succ a
        h = multiplicationNIsCommutative (succ a) (succ b)
        res : (pr1 : 0 <N succ b +N a *N succ b) → (pr2 : 0 <N succ a +N b *N succ a) → positive (succ a *N succ b) pr1 ≡ positive (succ b *N succ a) pr2
        res pr1 pr2 rewrite h = posIsPos pr1 pr2
    multiplicationZ'IsCommutative (positive zero (le x ())) zZero
    multiplicationZ'IsCommutative (positive (succ a) x) zZero = refl
    multiplicationZ'IsCommutative zZero (negative zero (le x ()))
    multiplicationZ'IsCommutative zZero (negative (succ a) x) = refl
    multiplicationZ'IsCommutative zZero (positive zero (le x ()))
    multiplicationZ'IsCommutative zZero (positive (succ a) x) = refl
    multiplicationZ'IsCommutative zZero zZero = refl

    multiplicationZIsCommutative : (a b : ℤ) → (a *Z b ≡ b *Z a)
    multiplicationZIsCommutative a b = res
      where
        help : convertZ' (convertZ a *Z' convertZ b) ≡ convertZ' (convertZ b *Z' convertZ a)
        help = applyEquality convertZ' (multiplicationZ'IsCommutative (convertZ a) (convertZ b))
        res : a *Z b ≡ b *Z a
        res rewrite zIsZ a | zIsZ b = help

    negSuccIsNotNonneg : (a b : ℕ) → (negSucc a ≡ nonneg b) → False
    negSuccIsNotNonneg zero b ()
    negSuccIsNotNonneg (succ a) b ()

    negSuccInjective : {a b : ℕ} → (negSucc a ≡ negSucc b) → a ≡ b
    negSuccInjective refl = refl

    zeroMultInZLeft : (a : ℤ) → (nonneg zero) *Z a ≡ (nonneg zero)
    zeroMultInZLeft a = identityOfIndiscernablesLeft (a *Z nonneg zero) (nonneg zero) (nonneg zero *Z a) _≡_ (multiplyWithZero a) (multiplicationZIsCommutative a (nonneg zero))

    additionZeroDoesNothing : (a : ℤ) → (a +Z nonneg zero ≡ a)
    additionZeroDoesNothing (nonneg zero) = refl
    additionZeroDoesNothing (nonneg (succ x)) = applyEquality nonneg (applyEquality succ (addZeroRight x))
    additionZeroDoesNothing (negSucc x) = refl

    canSubtractOne : (a : ℤ) (b : ℕ) → negSucc zero +Z a ≡ negSucc (succ b) → a ≡ negSucc b
    canSubtractOne (nonneg zero) b pr = i
      where
        simplified : negSucc zero ≡ negSucc (succ b)
        simplified = identityOfIndiscernablesLeft (negSucc zero +Z nonneg zero) (negSucc (succ b)) (negSucc zero) _≡_ pr refl
        removeNegsucc : zero ≡ succ b
        removeNegsucc = negSuccInjective simplified
        f : False
        f = succIsNonzero (equalityCommutative removeNegsucc)
        i : (nonneg zero) ≡ negSucc b
        i = exFalso f
    canSubtractOne (nonneg (succ x)) b pr = exFalso (negSuccIsNotNonneg (succ b) x (equalityCommutative pr))
    canSubtractOne (negSucc x) .x refl = refl

    canAddOne : (a : ℤ) (b : ℕ) → a ≡ negSucc b → negSucc zero +Z a ≡ negSucc (succ b)
    canAddOne (nonneg x) b ()
    canAddOne (negSucc x) .x refl = refl

    canAddOneReversed : (a : ℤ) (b : ℕ) → a ≡ negSucc b → a +Z negSucc zero ≡ negSucc (succ b)
    canAddOneReversed a b pr = identityOfIndiscernablesLeft (negSucc zero +Z a) (negSucc (succ b)) (a +Z negSucc zero) _≡_ (canAddOne a b pr) (additionZIsCommutative (negSucc zero) a)

    addToNegativeSelf : (a : ℕ) → negSucc a +Z nonneg a ≡ negSucc zero
    addToNegativeSelf zero = refl
    addToNegativeSelf (succ a) = addToNegativeSelf a

    multiplicativeIdentityOneZNegsucc : (a : ℕ) → (negSucc a *Z nonneg (succ zero) ≡ negSucc a)
    multiplicativeIdentityOneZNegsucc zero = refl
    multiplicativeIdentityOneZNegsucc (succ x) rewrite multiplicationZIsCommutative (negSucc (succ x)) (nonneg 1) | additionNIsCommutative x 0 = refl

    multiplicativeIdentityOneZ : (a : ℤ) → (a *Z nonneg (succ zero) ≡ a)
    multiplicativeIdentityOneZ (nonneg zero) rewrite multiplicationZIsCommutative (nonneg 0) (nonneg 1) = refl
    multiplicativeIdentityOneZ (nonneg (succ x)) rewrite multiplicationZIsCommutative (nonneg (succ x)) (nonneg 1) | additionNIsCommutative x 0 = refl
    multiplicativeIdentityOneZ (negSucc x) = multiplicativeIdentityOneZNegsucc (x)

    multiplicativeIdentityOneZLeft : (a : ℤ) → (nonneg (succ zero)) *Z a ≡ a
    multiplicativeIdentityOneZLeft a = identityOfIndiscernablesLeft (a *Z nonneg (succ zero)) a (nonneg (succ zero) *Z a) _≡_ (multiplicativeIdentityOneZ a) (multiplicationZIsCommutative a (nonneg (succ zero)))

    -- Define the equivalence of negSucc + nonneg = nonneg with the corresponding statements of naturals

    negSuccPlusNonnegNonneg : (a : ℕ) → (b : ℕ) → (c : ℕ) → (negSucc a +Z (nonneg b) ≡ nonneg c) → b ≡ c +N succ a
    negSuccPlusNonnegNonneg zero zero c ()
    negSuccPlusNonnegNonneg zero (succ b) .b refl rewrite succExtracts b zero | addZeroRight b = refl
    negSuccPlusNonnegNonneg (succ a) zero c ()
    negSuccPlusNonnegNonneg (succ a) (succ b) c pr with negSuccPlusNonnegNonneg a b c pr
    ... | prev = identityOfIndiscernablesRight (succ b) (succ (c +N succ a)) (c +N succ (succ a)) _≡_ (applyEquality succ prev) (equalityCommutative (succExtracts c (succ a)))

    negSuccPlusNonnegNonnegConverse : (a : ℕ) → (b : ℕ) → (c : ℕ) → (b ≡ c +N succ a) → (negSucc a +Z (nonneg b) ≡ nonneg c)
    negSuccPlusNonnegNonnegConverse zero zero c pr rewrite succExtracts c zero = naughtE pr
    negSuccPlusNonnegNonnegConverse zero (succ b) c pr rewrite additionNIsCommutative c 1 with succInjective pr
    ... | pr' = applyEquality nonneg pr'
    negSuccPlusNonnegNonnegConverse (succ a) zero c pr rewrite succExtracts c (succ a) = naughtE pr
    negSuccPlusNonnegNonnegConverse (succ a) (succ b) c pr rewrite succExtracts c (succ a) with succInjective pr
    ... | pr' = negSuccPlusNonnegNonnegConverse a b c pr'

    -- Define the equivalence of negSucc + nonneg = negSucc with the corresponding statements of naturals

    negSuccPlusNonnegNegsucc : (a b c : ℕ) → (negSucc a +Z (nonneg b) ≡ negSucc c) → c +N b ≡ a
    negSuccPlusNonnegNegsucc zero zero .0 refl = refl
    negSuccPlusNonnegNegsucc zero (succ b) c ()
    negSuccPlusNonnegNegsucc (succ a) zero .(succ a) refl rewrite addZeroRight a = refl
    negSuccPlusNonnegNegsucc (succ a) (succ b) c pr with negSuccPlusNonnegNegsucc a b c pr
    ... | pr' = identityOfIndiscernablesLeft (succ (c +N b)) (succ a) (c +N succ b) _≡_ (applyEquality succ pr') (equalityCommutative (succExtracts c b))

    negSuccPlusNonnegNegsuccConverse : (a b c : ℕ) → (c +N b ≡ a) → (negSucc a +Z (nonneg b) ≡ negSucc c)
    negSuccPlusNonnegNegsuccConverse zero zero c pr rewrite addZeroRight c = applyEquality negSucc (equalityCommutative pr)
    negSuccPlusNonnegNegsuccConverse zero (succ b) c pr rewrite succExtracts c b = naughtE (equalityCommutative pr)
    negSuccPlusNonnegNegsuccConverse (succ a) zero c pr rewrite addZeroRight c = applyEquality negSucc (equalityCommutative pr)
    negSuccPlusNonnegNegsuccConverse (succ a) (succ b) c pr rewrite succExtracts c b = negSuccPlusNonnegNegsuccConverse a b c (succInjective pr)

    -- Define the impossibility of negSucc + negSucc = nonneg
    negSuccPlusNegSuccIsNegative : (a b c : ℕ) → ((negSucc a) +Z (negSucc b) ≡ nonneg c) → False
    negSuccPlusNegSuccIsNegative zero b c ()
    negSuccPlusNegSuccIsNegative (succ a) b c ()

    -- Define the equivalence of negSucc + negSucc = negSucc
    negSuccPlusNegSuccNegSucc : (a b c : ℕ) → (negSucc a) +Z (negSucc b) ≡ (negSucc c) → succ (a +N b) ≡ c
    negSuccPlusNegSuccNegSucc zero b .(succ b) refl = refl
    negSuccPlusNegSuccNegSucc (succ a) b .(succ (a +N succ b)) refl = applyEquality succ (equalityCommutative (succExtracts a b))

    negSuccPlusNegSuccNegSuccConverse : (a b c : ℕ) → succ (a +N b) ≡ c → (negSucc a) +Z (negSucc b) ≡ negSucc c
    negSuccPlusNegSuccNegSuccConverse zero b c pr = applyEquality negSucc pr
    negSuccPlusNegSuccNegSuccConverse (succ a) b zero ()
    negSuccPlusNegSuccNegSuccConverse (succ a) b (succ c) pr rewrite succExtracts a b = applyEquality negSucc pr

    -- Define the equivalence of nonneg + nonneg = nonneg
    nonnegPlusNonnegNonneg : (a b c : ℕ) → nonneg a +Z nonneg b ≡ nonneg c → a +N b ≡ c
    nonnegPlusNonnegNonneg a b c pr rewrite addingNonnegIsHom a b = nonnegInj pr
      where
        nonnegInj : {x y : ℕ} → (pr : nonneg x ≡ nonneg y) → x ≡ y
        nonnegInj {x} {.x} refl = refl

    nonnegPlusNonnegNonnegConverse : (a b c : ℕ) → a +N b ≡ c → nonneg a +Z nonneg b ≡ nonneg c
    nonnegPlusNonnegNonnegConverse a b c pr rewrite addingNonnegIsHom a b = applyEquality nonneg pr

    nonnegIsNotNegsucc : {x y : ℕ} → nonneg x ≡ negSucc y → False
    nonnegIsNotNegsucc {x} {y} ()

    -- Define the impossibility of nonneg + nonneg = negSucc
    nonnegPlusNonnegNegsucc : (a b c : ℕ) → nonneg a +Z nonneg b ≡ negSucc c → False
    nonnegPlusNonnegNegsucc a b c pr rewrite addingNonnegIsHom a b = nonnegIsNotNegsucc pr

    -- Move negSucc to other side of equation
    moveNegsucc : (a : ℕ) (b c : ℤ) → (negSucc a) +Z b ≡ c → b ≡ c +Z (nonneg (succ a))
    moveNegsucc a (nonneg x) (nonneg y) pr with (negSuccPlusNonnegNonneg a x y pr)
    ... | pr' = identityOfIndiscernablesRight (nonneg x) (nonneg (y +N succ a)) (nonneg y +Z nonneg (succ a)) _≡_ (applyEquality nonneg pr') (equalityCommutative (addingNonnegIsHom y (succ a)))
    moveNegsucc a (nonneg x) (negSucc y) pr with negSuccPlusNonnegNegsucc a x y pr
    ... | pr' = equalityCommutative (negSuccPlusNonnegNonnegConverse y (succ a) x (g {a} {x} {y} (applyEquality succ pr')))
      where
        g : {a x y : ℕ} → succ (y +N x) ≡ succ a → succ a ≡ x +N succ y
        g {a} {x} {y} p rewrite additionNIsCommutative y x | succExtracts x y = equalityCommutative p
    moveNegsucc a (negSucc x) (nonneg y) pr = exFalso (negSuccPlusNegSuccIsNegative a x y pr)
    moveNegsucc a (negSucc x) (negSucc y) pr with negSuccPlusNegSuccNegSucc a x y pr
    ... | pr' = equalityCommutative (negSuccPlusNonnegNegsuccConverse y (succ a) x g)
      where
        g : x +N succ a ≡ y
        g rewrite succExtracts x a | additionNIsCommutative a x = pr'

    moveNegsuccConverse : (a : ℕ) → (b c : ℤ) → (b ≡ c +Z (nonneg (succ a))) → (negSucc a) +Z b ≡ c
    moveNegsuccConverse zero (nonneg x) (nonneg y) pr with nonnegPlusNonnegNonneg y 1 x (equalityCommutative pr)
    ... | pr' rewrite (equalityCommutative (succIsAddOne y)) = g
      where
        g : negSucc 0 +Z nonneg x ≡ nonneg y
        g rewrite equalityCommutative pr' = refl
    moveNegsuccConverse zero (nonneg x) (negSucc y) pr with moveNegsucc y (nonneg 1) (nonneg x) (equalityCommutative pr)
    ... | pr' rewrite addingNonnegIsHom x (succ y) = g x y (nonnegInjective pr')
      where
        g : (x y : ℕ) → (1 ≡ (x +N succ y)) → negSucc 0 +Z nonneg x ≡ negSucc y
        g zero zero pr = refl
        g zero (succ y) ()
        g (succ x) y pr = naughtE (identityOfIndiscernablesRight zero (x +N succ y) (succ (x +N y)) _≡_ (succInjective pr) (succExtracts x y))
    moveNegsuccConverse zero (negSucc x) (nonneg y) pr = exFalso (nonnegPlusNonnegNegsucc y 1 x (equalityCommutative pr))
    moveNegsuccConverse zero (negSucc x) (negSucc y) pr with negSuccPlusNonnegNegsucc y 1 x (equalityCommutative pr)
    ... | pr' = applyEquality negSucc g
      where
        g : succ x ≡ y
        g rewrite additionNIsCommutative x 1 = pr'
    moveNegsuccConverse (succ a) (nonneg x) (nonneg y) pr with nonnegPlusNonnegNonneg y (succ (succ a)) x (equalityCommutative pr)
    ... | pr' = negSuccPlusNonnegNonnegConverse (succ a) x y (equalityCommutative pr')
    moveNegsuccConverse (succ a) (nonneg x) (negSucc y) pr with negSuccPlusNonnegNonneg y (succ (succ a)) x (equalityCommutative pr)
    ... | pr' = negSuccPlusNonnegNegsuccConverse (succ a) x y (g a x y pr')
      where
        g : (a x y : ℕ) → succ (succ a) ≡ x +N succ y → y +N x ≡ succ a
        g a x y pr rewrite succExtracts x y | additionNIsCommutative x y = equalityCommutative (succInjective pr)
    moveNegsuccConverse (succ a) (negSucc x) (nonneg z) pr = exFalso (nonnegPlusNonnegNegsucc z (succ (succ a)) x (equalityCommutative pr))
    moveNegsuccConverse (succ a) (negSucc x) (negSucc z) pr with negSuccPlusNonnegNegsucc z (succ (succ a)) x (equalityCommutative pr)
    ... | pr' = applyEquality negSucc (g a x z pr')
      where
        g : (a x z : ℕ) → x +N succ (succ a) ≡ z → succ (a +N succ x) ≡ z
        g a x z pr rewrite succExtracts x (succ a) = identityOfIndiscernablesLeft (succ (x +N succ a)) z (succ (a +N succ x)) _≡_ pr (applyEquality succ (s x a))
          where
            s : (x a : ℕ) → x +N succ a ≡ a +N succ x
            s x a rewrite succCanMove a x = additionNIsCommutative x (succ a)

    -- By this point, any statement about addition can be moved from N into Z and from Z into N by applying moveNegSucc and its converse to eliminate any adding of negSucc.

    lessIsPreservedNToZNegsucc : {a b : ℕ} → (a <N b) → ((negSucc b) <Z negSucc a)
    lessIsPreservedNToZNegsucc {a} {b} (le x proof) = record { x = x ; proof = pr }
      where
        pr : nonneg (succ x) +Z negSucc b ≡ negSucc a
        pr rewrite additionZIsCommutative (nonneg (succ x)) (negSucc b) = moveNegsuccConverse b (nonneg (succ x)) (negSucc a) (equalityCommutative (moveNegsuccConverse a (nonneg (succ b)) (nonneg (succ x)) (applyEquality nonneg (applyEquality succ proof'))))
          where
            proof' : b ≡ x +N succ a
            proof' rewrite additionNIsCommutative x a | additionNIsCommutative (succ a) x = equalityCommutative proof

    lessLemma : (a x : ℕ) → succ x +N a ≡ a → False
    lessLemma zero x pr = naughtE (equalityCommutative pr)
    lessLemma (succ a) x pr = lessLemma a x q
      where
        q : succ x +N a ≡ a
        q rewrite additionNIsCommutative a (succ x) | additionNIsCommutative x a | additionNIsCommutative (succ a) x = succInjective pr

    sumOfNegsucc : (a b : ℕ) → (negSucc a +Z negSucc b) ≡ negSucc (succ (a +N b))
    sumOfNegsucc a b = negSuccPlusNegSuccNegSuccConverse a b (succ (a +N b)) refl

    additionZInjLemma : {a b c : ℕ} → (nonneg a ≡ (nonneg a +Z nonneg b) +Z nonneg (succ c)) → False
    additionZInjLemma {a} {b} {c} pr = cannotAddKeepingEquality a (c +N b) pr2''
      where
        pr'' : nonneg a ≡ nonneg (a +N b) +Z nonneg (succ c)
        pr'' = identityOfIndiscernablesRight (nonneg a) ((nonneg a +Z nonneg b) +Z nonneg (succ c)) (nonneg (a +N b) +Z nonneg (succ c)) _≡_ pr (applyEquality (λ i → i +Z nonneg (succ c)) (addingNonnegIsHom a b))
        pr''' : nonneg a ≡ nonneg ((a +N b) +N succ c)
        pr''' = identityOfIndiscernablesRight (nonneg a) (nonneg (a +N b) +Z nonneg (succ c)) (nonneg ((a +N b) +N succ c)) _≡_ pr'' (addingNonnegIsHom (a +N b) (succ c))
        pr2 : a ≡ (a +N b) +N succ c
        pr2 = nonnegInjective pr'''
        pr2' : a ≡ a +N (b +N succ c)
        pr2' = identityOfIndiscernablesRight a ((a +N b) +N succ c) (a +N (b +N succ c)) _≡_ pr2 (additionNIsAssociative a b (succ c))
        pr2'' : a ≡ a +N succ (c +N b)
        pr2'' rewrite additionNIsCommutative (succ c) b = pr2'

    additionZInjectiveFirstLemma : (a : ℕ) → (b c : ℤ) → (nonneg a +Z b ≡ nonneg a +Z c) → (b ≡ c)
    additionZInjectiveFirstLemma a (nonneg b) (nonneg c) pr rewrite (addingNonnegIsHom a b) | (addingNonnegIsHom a c) = applyEquality nonneg (canSubtractFromEqualityLeft {a} pr')
      where
        pr' : a +N b ≡ a +N c
        pr' = nonnegInjective pr
    additionZInjectiveFirstLemma a (nonneg b) (negSucc c) pr = exFalso (additionZInjLemma pr')
      where
        pr' : nonneg a ≡ (nonneg a +Z nonneg b) +Z nonneg (succ c)
        pr' rewrite additionZIsCommutative (nonneg a) (negSucc c) = moveNegsucc c (nonneg a) (nonneg a +Z nonneg b) (equalityCommutative pr)
    additionZInjectiveFirstLemma a (negSucc b) (nonneg x) pr = exFalso (additionZInjLemma pr')
      where
        pr' : nonneg a ≡ (nonneg a +Z nonneg x) +Z nonneg (succ b)
        pr' rewrite additionZIsCommutative (nonneg a) (negSucc b) = moveNegsucc b (nonneg a) (nonneg a +Z nonneg x) pr
    additionZInjectiveFirstLemma zero (negSucc zero) (negSucc x) pr = pr
    additionZInjectiveFirstLemma zero (negSucc (succ b)) (negSucc x) pr = pr
    additionZInjectiveFirstLemma (succ a) (negSucc zero) (negSucc x) pr = applyEquality negSucc (equalityCommutative qr'')
      where
        pr1 : negSucc x +Z nonneg (succ a) ≡ nonneg a
        pr1 rewrite additionZIsCommutative (nonneg (succ a)) (negSucc x) = equalityCommutative pr
        pr' : nonneg a +Z nonneg (succ x) ≡ nonneg (succ a)
        pr' = equalityCommutative (moveNegsucc x (nonneg (succ a)) (nonneg a) pr1)
        pr'' : nonneg (a +N succ x) ≡ nonneg (succ a)
        pr'' rewrite equalityCommutative (addingNonnegIsHom a (succ x)) = pr'
        pr''' : a +N succ x ≡ succ a
        pr''' = nonnegInjective pr''
        pr'''' : succ x +N a ≡ succ a
        pr'''' rewrite additionNIsCommutative (succ x) a = pr'''
        qr : succ (a +N x) ≡ succ a
        qr rewrite additionNIsCommutative a x = pr''''
        qr' : a +N x ≡ a +N 0
        qr' rewrite addZeroRight a = succInjective qr
        qr'' : x ≡ 0
        qr'' = canSubtractFromEqualityLeft {a} qr'
    additionZInjectiveFirstLemma (succ a) (negSucc (succ b)) (negSucc zero) pr = naughtE qr
      where
        pr' : nonneg a ≡ nonneg a +Z nonneg (succ b)
        pr' rewrite additionZIsCommutative (nonneg a) (negSucc b) = moveNegsucc b (nonneg a) (nonneg a) pr
        pr'' : nonneg a ≡ nonneg (a +N succ b)
        pr'' rewrite equalityCommutative (addingNonnegIsHom a (succ b)) = pr'
        pr''' : a +N 0 ≡ a +N succ b
        pr''' rewrite addZeroRight a = nonnegInjective pr''
        qr : 0 ≡ succ b
        qr = canSubtractFromEqualityLeft {a} pr'''
    additionZInjectiveFirstLemma (succ a) (negSucc (succ b)) (negSucc (succ x)) pr = go b x pr''
      where
        pr' : negSucc b ≡ negSucc x
        pr' = additionZInjectiveFirstLemma a (negSucc b) (negSucc x) pr
        pr'' : b ≡ x
        pr'' = negSuccInjective pr'
        go : (b x : ℕ) → (b ≡ x) → negSucc (succ b) ≡ negSucc (succ x)
        go b .b refl = refl

    additionZInjectiveSecondLemmaLemma : (a : ℕ) (b : ℕ) (c : ℕ) → (negSucc a +Z nonneg b ≡ negSucc a +Z negSucc c) → nonneg b ≡ negSucc c
    additionZInjectiveSecondLemmaLemma zero zero zero pr = naughtE (negSuccInjective pr)
    additionZInjectiveSecondLemmaLemma zero zero (succ c) pr = naughtE (negSuccInjective pr)
    additionZInjectiveSecondLemmaLemma zero (succ b) c pr = exFalso (nonnegIsNotNegsucc pr)
    additionZInjectiveSecondLemmaLemma (succ a) zero c pr = naughtE (canSubtractFromEqualityLeft {succ a} pr')
      where
        pr' : succ a +N zero ≡ succ a +N succ c
        pr' rewrite addZeroRight (succ a) = negSuccInjective pr
    additionZInjectiveSecondLemmaLemma (succ a) (succ b) c pr = naughtE r
      where
        pr' : negSucc (succ (a +N succ c)) +Z nonneg (succ a) ≡ nonneg b
        pr' = equalityCommutative (moveNegsucc a (nonneg b) (negSucc (succ (a +N succ c))) pr)
        pr'' : nonneg (succ a) ≡ nonneg b +Z nonneg (succ (succ (a +N succ c)))
        pr'' = moveNegsucc (succ (a +N succ c)) (nonneg (succ a)) (nonneg b) pr'
        pr''' : nonneg (succ a) ≡ nonneg (b +N succ (succ (a +N succ c)))
        pr''' rewrite equalityCommutative (addingNonnegIsHom b (succ (succ (a +N succ c)))) = pr''
        pr'''' : succ a ≡ b +N ((succ (succ a)) +N succ c)
        pr'''' = nonnegInjective pr'''
        q : succ a ≡ (b +N (succ (succ a))) +N succ c
        q = identityOfIndiscernablesRight (succ a) (b +N ((succ (succ a)) +N succ c)) ((b +N (succ (succ a))) +N succ c) _≡_ pr'''' (equalityCommutative (additionNIsAssociative b (succ (succ a)) (succ c)))
        moveSucc : (a b : ℕ) → a +N succ b ≡ succ a +N b
        moveSucc a b rewrite additionNIsCommutative a (succ b) | additionNIsCommutative a b = refl
        q' : succ a ≡ (succ b +N succ a) +N succ c
        q' = identityOfIndiscernablesRight (succ a) ((b +N succ (succ a)) +N succ c) ((succ b +N succ a) +N succ c) _≡_ q (applyEquality (λ t → t +N succ c) (moveSucc b (succ a)))
        q'' : succ a ≡ (succ a +N succ b) +N succ c
        q'' = identityOfIndiscernablesRight (succ a) ((succ b +N succ a) +N succ c) ((succ a +N succ b) +N succ c) _≡_ q' (applyEquality (λ t → t +N succ c) (additionNIsCommutative (succ b) (succ a)))
        q''' : succ a ≡ succ a +N (succ b +N succ c)
        q''' rewrite equalityCommutative (additionNIsAssociative (succ a) (succ b) (succ c)) = q''
        q'''' : succ a +N zero ≡ succ a +N (succ b +N succ c)
        q'''' rewrite addZeroRight (succ a) = q'''
        r : zero ≡ succ b +N succ c
        r = canSubtractFromEqualityLeft {succ a} q''''

    additionZInjectiveSecondLemma : (a : ℕ) (b c : ℤ) → (negSucc a +Z b ≡ negSucc a +Z c) → b ≡ c
    additionZInjectiveSecondLemma zero (nonneg zero) (nonneg zero) pr = refl
    additionZInjectiveSecondLemma zero (nonneg zero) (nonneg (succ c)) pr = exFalso (nonnegIsNotNegsucc (equalityCommutative pr))
    additionZInjectiveSecondLemma zero (nonneg (succ b)) (nonneg zero) pr = exFalso (nonnegIsNotNegsucc pr)
    additionZInjectiveSecondLemma zero (nonneg (succ b)) (nonneg (succ c)) pr rewrite additionZIsCommutative (negSucc zero) (nonneg b) | additionZIsCommutative (negSucc zero) (nonneg c) = applyEquality (λ t → nonneg (succ t)) pr'
      where
        pr' : b ≡ c
        pr' = nonnegInjective pr
    additionZInjectiveSecondLemma zero (nonneg zero) (negSucc c) pr = naughtE pr'
      where
        pr' : zero ≡ succ c
        pr' = negSuccInjective pr
    additionZInjectiveSecondLemma zero (negSucc b) (nonneg zero) pr = naughtE (negSuccInjective (equalityCommutative pr))
    additionZInjectiveSecondLemma zero (negSucc b) (nonneg (succ c)) pr = exFalso (nonnegIsNotNegsucc (equalityCommutative pr))
    additionZInjectiveSecondLemma zero (negSucc b) (negSucc c) pr = applyEquality negSucc (succInjective pr')
      where
        pr' : succ b ≡ succ c
        pr' = negSuccInjective pr
    additionZInjectiveSecondLemma zero (nonneg (succ b)) (negSucc c) pr = exFalso (nonnegIsNotNegsucc pr)
    additionZInjectiveSecondLemma (succ a) (nonneg zero) (nonneg zero) pr = refl
    additionZInjectiveSecondLemma (succ a) (nonneg zero) (nonneg (succ c)) pr = exFalso (nonnegIsNotNegsucc pr'')
      where
        pr' : nonneg c ≡ negSucc (succ a) +Z nonneg (succ a)
        pr' = moveNegsucc a (nonneg c) (negSucc (succ a)) (equalityCommutative pr)
        pr'' : nonneg c ≡ negSucc zero
        pr'' rewrite equalityCommutative (addToNegativeSelf (succ a)) = pr'
    additionZInjectiveSecondLemma (succ a) (nonneg (succ b)) (nonneg zero) pr = exFalso (nonnegIsNotNegsucc pr'')
      where
        pr' : nonneg b ≡ negSucc (succ a) +Z nonneg (succ a)
        pr' = moveNegsucc a (nonneg b) (negSucc (succ a)) pr
        pr'' : nonneg b ≡ negSucc zero
        pr'' rewrite equalityCommutative (addToNegativeSelf (succ a)) = pr'
    additionZInjectiveSecondLemma (succ a) (nonneg (succ b)) (nonneg (succ c)) pr = applyEquality (λ t → nonneg (succ t)) pr''
      where
        pr' : nonneg b ≡ nonneg c
        pr' = additionZInjectiveSecondLemma a (nonneg b) (nonneg c) pr
        pr'' : b ≡ c
        pr'' = nonnegInjective pr'
    additionZInjectiveSecondLemma (succ a) (nonneg zero) (negSucc c) pr = naughtE pr''
      where
        pr' : succ a +N zero ≡ succ a +N succ c
        pr' rewrite addZeroRight a = negSuccInjective pr
        pr'' : zero ≡ succ c
        pr'' = canSubtractFromEqualityLeft {succ a} pr'
    additionZInjectiveSecondLemma (succ a) (nonneg (succ b)) (negSucc c) pr = additionZInjectiveSecondLemmaLemma (succ a) (succ b) c pr
    additionZInjectiveSecondLemma (succ a) (negSucc b) (nonneg c) pr = equalityCommutative pr'
      where
        pr' : nonneg c ≡ negSucc b
        pr' = additionZInjectiveSecondLemmaLemma (succ a) c b (equalityCommutative pr)
    additionZInjectiveSecondLemma (succ a) (negSucc b) (negSucc c) pr = applyEquality negSucc pr'''
      where
        pr' : succ a +N succ b ≡ succ a +N succ c
        pr' = negSuccInjective pr
        pr'' : succ b ≡ succ c
        pr'' = canSubtractFromEqualityLeft {succ a} pr'
        pr''' : b ≡ c
        pr''' = succInjective pr''

    additionZInjective : (a b c : ℤ) → (a +Z b ≡ a +Z c) → b ≡ c
    additionZInjective (nonneg a) b c pr = additionZInjectiveFirstLemma a b c pr
    additionZInjective (negSucc a) b c pr = additionZInjectiveSecondLemma a b c pr

    addNonnegSucc : (a : ℤ) → (b c : ℕ) → (a +Z nonneg b ≡ nonneg c) → a +Z nonneg (succ b) ≡ nonneg (succ c)
    addNonnegSucc (nonneg x) b c pr rewrite addingNonnegIsHom x (succ b) | addingNonnegIsHom x b = applyEquality nonneg g
      where
        p : x +N b ≡ c
        p = nonnegInjective pr
        g : x +N succ b ≡ succ c
        g = identityOfIndiscernablesLeft (succ (x +N b)) (succ c) (x +N succ b) _≡_ (applyEquality succ p) (equalityCommutative (succExtracts x b))
    addNonnegSucc (negSucc x) b c pr = negSuccPlusNonnegNonnegConverse x (succ b) (succ c) (applyEquality succ p')
      where
        p' : b ≡ c +N succ x
        p' = negSuccPlusNonnegNonneg x b c pr

    addNonnegSuccLemma : (a x d : ℕ) → (negSucc (succ a) +Z nonneg zero ≡ negSucc (succ x) +Z nonneg (succ d)) → negSucc (succ a) +Z nonneg (succ zero) ≡ negSucc (succ x) +Z nonneg (succ (succ d))
    addNonnegSuccLemma a x d pr = s
      where
        p' : negSucc (succ a) +Z nonneg (succ x) ≡ nonneg d
        p' = equalityCommutative (moveNegsucc x (nonneg d) (negSucc (succ a)) (equalityCommutative pr))
        p'' : nonneg (succ x) ≡ nonneg d +Z nonneg (succ (succ a))
        p'' = moveNegsucc (succ a) (nonneg (succ x)) (nonneg d) p'
        p''' : nonneg (succ x) ≡ nonneg (d +N succ (succ a))
        p''' rewrite equalityCommutative (addingNonnegIsHom d (succ (succ a))) = p''
        q : succ x ≡ d +N succ (succ a)
        q = nonnegInjective p'''
        q' : succ x ≡ succ (succ a) +N d
        q' rewrite additionNIsCommutative (succ (succ a)) d = q
        q'' : succ x ≡ succ d +N succ a
        q'' rewrite additionNIsCommutative d (succ a) = q'
        q''' : succ x ≡ succ a +N succ d
        q''' rewrite additionNIsCommutative (succ a) (succ d) = q''
        r : nonneg (succ x) ≡ nonneg (succ a +N succ d)
        r = applyEquality nonneg q'''
        r' : nonneg (succ x) ≡ nonneg (succ a) +Z nonneg (succ d)
        r' = identityOfIndiscernablesRight (nonneg (succ x)) (nonneg (succ a +N succ d)) (nonneg (succ a) +Z nonneg (succ d)) _≡_ r (addingNonnegIsHom (succ a) (succ d))
        r'' : nonneg (succ x) ≡ nonneg (succ d) +Z nonneg (succ a)
        r'' rewrite additionZIsCommutative (nonneg (succ d)) (nonneg (succ a)) = r'
        r''' : nonneg (succ d) ≡ negSucc a +Z nonneg (succ x)
        r''' = equalityCommutative (moveNegsuccConverse a (nonneg (succ x)) (nonneg (succ d)) r'')
        s : negSucc a ≡ negSucc x +Z nonneg (succ d)
        s = equalityCommutative (moveNegsuccConverse x (nonneg (succ d)) (negSucc a) r''')

    addNonnegSucc' : (a b : ℤ) → (c d : ℕ) → (a +Z nonneg c ≡ b +Z nonneg d) → a +Z nonneg (succ c) ≡ b +Z nonneg (succ d)
    addNonnegSucc' a (nonneg x) c d pr rewrite addingNonnegIsHom x (succ d) | addingNonnegIsHom x d | addNonnegSucc a c (x +N d) pr = applyEquality nonneg (equalityCommutative (succExtracts x d))
    addNonnegSucc' (nonneg a) (negSucc x) c d pr = equalityCommutative (moveNegsuccConverse x (nonneg (succ d)) ((nonneg a) +Z nonneg (succ c)) (equalityCommutative q))
      where
        p : ((nonneg a) +Z nonneg c) +Z nonneg (succ x) ≡ nonneg d
        p = equalityCommutative (moveNegsucc x (nonneg d) ((nonneg a) +Z nonneg c) (equalityCommutative pr))
        p' : nonneg ((a +N c) +N succ x) ≡ nonneg d
        p' = identityOfIndiscernablesLeft ((nonneg a +Z nonneg c) +Z nonneg (succ x)) (nonneg d) (nonneg ((a +N c) +N succ x)) _≡_ p g
          where
            g : (nonneg a +Z nonneg c) +Z nonneg (succ x) ≡ nonneg ((a +N c) +N succ x)
            g rewrite addingNonnegIsHom a c | addingNonnegIsHom (a +N c) (succ x) = refl
        p'' : (a +N c) +N succ x ≡ d
        p'' = nonnegInjective p'
        p''' : (a +N succ c) +N succ x ≡ succ d
        p''' = identityOfIndiscernablesLeft (succ (a +N c) +N succ x) (succ d) ((a +N succ c) +N succ x) _≡_ (applyEquality succ p'') g
          where
            g : succ ((a +N c) +N succ x) ≡ (a +N succ c) +N succ x
            g = applyEquality (λ i → i +N succ x) {succ (a +N c)} {a +N succ c} (equalityCommutative (succExtracts a c))
        q : (nonneg a +Z nonneg (succ c)) +Z nonneg (succ x) ≡ nonneg (succ d)
        q rewrite (addingNonnegIsHom a (succ c)) | addingNonnegIsHom (a +N succ c) (succ x) = applyEquality nonneg p'''

    addNonnegSucc' (negSucc a) (negSucc x) c d pr with (inspect (negSucc x +Z nonneg d))
    addNonnegSucc' (negSucc a) (negSucc x) c d pr | (nonneg int) with≡ p = identityOfIndiscernablesRight (negSucc a +Z nonneg (succ c)) (nonneg (succ int)) (negSucc x +Z nonneg (succ d)) _≡_ (addNonnegSucc (negSucc a) c int (transitivity pr p)) (equalityCommutative (addNonnegSucc (negSucc x) d int p))
    addNonnegSucc' (negSucc zero) (negSucc zero) c d pr | negSucc int with≡ p = additionZInjective (negSucc zero) (nonneg c) (nonneg d) pr
      where
        pr' : nonneg c ≡ (negSucc zero +Z nonneg d) +Z nonneg 1
        pr' = moveNegsucc zero (nonneg c) (negSucc zero +Z nonneg d) pr
    addNonnegSucc' (negSucc zero) (negSucc (succ x)) zero d pr | negSucc int with≡ p = equalityCommutative (moveNegsuccConverse x (nonneg d) (nonneg zero) (equalityCommutative (applyEquality nonneg q')))
      where
        pr' : nonneg d ≡ (negSucc zero) +Z (nonneg (succ (succ x)))
        pr' = moveNegsucc (succ x) (nonneg d) (negSucc zero) (equalityCommutative pr)
        pr'' : nonneg (succ (succ x)) ≡ nonneg d +Z nonneg 1
        pr'' = moveNegsucc (zero) (nonneg (succ (succ x))) (nonneg d) (equalityCommutative pr')
        pr''' : nonneg (succ (succ x)) ≡ nonneg (d +N 1)
        pr''' rewrite equalityCommutative (addingNonnegIsHom d 1) = pr''
        pr'''' : succ (succ x) ≡ d +N 1
        pr'''' = nonnegInjective pr'''
        q : succ (succ x) ≡ succ d
        q rewrite additionNIsCommutative 1 d = pr''''
        q' : succ x ≡ d
        q' = succInjective q
    addNonnegSucc' (negSucc zero) (negSucc (succ x)) (succ c) zero pr | negSucc int with≡ p = exFalso (nonnegIsNotNegsucc pr)
    addNonnegSucc' (negSucc zero) (negSucc (succ x)) (succ c) (succ d) pr | negSucc int with≡ p = addNonnegSucc' (nonneg zero) (negSucc x) c d pr
    addNonnegSucc' (negSucc (succ a)) (negSucc zero) zero d pr | negSucc int with≡ p = naughtE q'
      where
        pr' : negSucc (succ a) +Z nonneg 1 ≡ nonneg d
        pr' = equalityCommutative (moveNegsucc zero (nonneg d) (negSucc (succ a)) (equalityCommutative pr))
        pr'' : nonneg 1 ≡ nonneg d +Z nonneg (succ (succ a))
        pr'' = moveNegsucc (succ a) (nonneg 1) (nonneg d) pr'
        pr''' : nonneg 1 ≡ nonneg (d +N succ (succ a))
        pr''' rewrite equalityCommutative (addingNonnegIsHom d (succ (succ a))) = pr''
        q : 1 ≡ succ (succ a) +N d
        q rewrite additionNIsCommutative (succ (succ a)) d = nonnegInjective pr'''
        q' : 0 ≡ succ a +N d
        q' = succInjective q
    addNonnegSucc' (negSucc (succ a)) (negSucc zero) (succ c) zero pr | negSucc int with≡ p = help
      where
        pr' : negSucc zero +Z nonneg (succ a) ≡ nonneg c
        pr' = equalityCommutative (moveNegsucc a (nonneg c) (negSucc zero) pr)
        pr'' : nonneg (succ a) ≡ nonneg c +Z nonneg 1
        pr'' = moveNegsucc zero (nonneg (succ a)) (nonneg c) pr'
        pr''' : nonneg (succ a) ≡ nonneg (c +N 1)
        pr''' rewrite equalityCommutative (addingNonnegIsHom c 1) = pr''
        q : succ a ≡ succ c
        q rewrite additionNIsCommutative 1 c = nonnegInjective pr'''
        q' : a ≡ c
        q' = succInjective q
        help : negSucc a +Z nonneg (succ c) ≡ nonneg zero
        help rewrite q' = additiveInverseExists c
    addNonnegSucc' (negSucc (succ a)) (negSucc zero) (succ c) (succ d) pr | negSucc int with≡ p = moveNegsuccConverse a (nonneg (succ c)) (nonneg (succ d)) q'
      where
        pr' : nonneg c ≡ nonneg d +Z nonneg (succ a)
        pr' = moveNegsucc a (nonneg c) (nonneg d) pr
        pr'' : nonneg c ≡ nonneg (d +N succ a)
        pr'' rewrite equalityCommutative (addingNonnegIsHom d (succ a)) = pr'
        pr''' : c ≡ d +N succ a
        pr''' = nonnegInjective pr''
        pr'''' : succ c ≡ succ d +N succ a
        pr'''' = applyEquality succ pr'''
        q : nonneg (succ c) ≡ nonneg (succ d +N succ a)
        q = applyEquality nonneg pr''''
        q' : nonneg (succ c) ≡ nonneg (succ d) +Z nonneg (succ a)
        q' rewrite addingNonnegIsHom (succ d) (succ a) = q
    addNonnegSucc' (negSucc (succ a)) (negSucc (succ x)) zero zero pr | negSucc int with≡ p = applyEquality negSucc (succInjective (negSuccInjective pr))
    addNonnegSucc' (negSucc (succ a)) (negSucc (succ x)) zero (succ d) pr | negSucc int with≡ p = addNonnegSuccLemma a x d pr
    addNonnegSucc' (negSucc (succ a)) (negSucc (succ x)) (succ c) zero pr | negSucc int with≡ p = equalityCommutative (addNonnegSuccLemma x a c (equalityCommutative pr))
    addNonnegSucc' (negSucc (succ a)) (negSucc (succ x)) (succ c) (succ d) pr | negSucc int with≡ p = addNonnegSucc' (negSucc a) (negSucc x) c d pr

    subtractNonnegSucc : (a : ℤ) → (b c : ℕ) → (a +Z nonneg (succ b) ≡ nonneg (succ c)) → a +Z nonneg b ≡ nonneg c
    subtractNonnegSucc (nonneg x) b c pr rewrite addingNonnegIsHom x (succ b) | addingNonnegIsHom x b = applyEquality nonneg g
      where
        p : succ (x +N b) ≡ succ c
        p rewrite succExtracts x b = nonnegInjective pr
        g : x +N b ≡ c
        g = succInjective p
    subtractNonnegSucc (negSucc x) b c pr = negSuccPlusNonnegNonnegConverse x b c (succInjective p')
      where
        p' : succ b ≡ succ (c +N succ x)
        p' = negSuccPlusNonnegNonneg x (succ b) (succ c) pr

    addNegsuccThenNonneg : (a : ℤ) (b c : ℕ) → (a +Z negSucc b) +Z nonneg (succ (c +N b)) ≡ a +Z nonneg c
    addNegsuccThenNonneg (nonneg zero) zero c rewrite addZeroRight c = refl
    addNegsuccThenNonneg (nonneg (succ x)) zero c rewrite addZeroRight c | addingNonnegIsHom x (succ c) = applyEquality nonneg (succExtracts x c)
    addNegsuccThenNonneg (nonneg zero) (succ b) c = moveNegsuccConverse b (nonneg (c +N succ b)) (nonneg c) (equalityCommutative (addingNonnegIsHom c (succ b)))
    addNegsuccThenNonneg (nonneg (succ x)) (succ b) c with addNegsuccThenNonneg (nonneg x) b c
    ... | prev = go
      where
        go : (nonneg x +Z negSucc b) +Z nonneg (succ (c +N succ b)) ≡ nonneg (succ (x +N c))
        go rewrite addingNonnegIsHom x c | succExtracts c b = p
          where
            p : (nonneg x +Z negSucc b) +Z nonneg (succ (succ (c +N b))) ≡ nonneg (succ (x +N c))
            p = addNonnegSucc (nonneg x +Z negSucc b) (succ (c +N b)) (x +N c) prev
    addNegsuccThenNonneg (negSucc x) zero c rewrite addZeroRight c | sumOfNegsucc x 0 | addZeroRight x = refl
    addNegsuccThenNonneg (negSucc x) (succ b) c with addNegsuccThenNonneg (negSucc x) b c
    ... | prev = go
      where
        p : nonneg c ≡ ((negSucc x +Z negSucc b) +Z nonneg (succ (c +N b))) +Z nonneg (succ x)
        p = moveNegsucc x (nonneg c) ((negSucc x +Z negSucc b) +Z nonneg (succ (c +N b))) (equalityCommutative prev)
        go : (negSucc x +Z negSucc (succ b)) +Z nonneg (succ (c +N succ b)) ≡ negSucc x +Z nonneg c
        go rewrite sumOfNegsucc x (succ b) | succExtracts c b = identityOfIndiscernablesLeft ((negSucc x +Z negSucc b) +Z nonneg (succ (c +N b))) (negSucc x +Z nonneg c) (negSucc (x +N succ b) +Z nonneg (succ (c +N b))) _≡_ prev (applyEquality (λ t → t +Z nonneg (succ (c +N b))) {negSucc x +Z negSucc b} {negSucc (x +N succ b)} (identityOfIndiscernablesRight (negSucc x +Z negSucc b) (negSucc (succ (x +N b))) (negSucc (x +N succ b)) _≡_ (sumOfNegsucc x b) (applyEquality negSucc (equalityCommutative (succExtracts x b)))))

    addNonnegThenNonneg : (a : ℤ) (b c : ℕ) → (a +Z nonneg b) +Z nonneg c ≡ a +Z nonneg (b +N c)
    addNonnegThenNonneg (nonneg x) b c rewrite addingNonnegIsHom x b | addingNonnegIsHom x (b +N c) | addingNonnegIsHom (x +N b) c = applyEquality nonneg (additionNIsAssociative x b c)
    addNonnegThenNonneg (negSucc x) b zero rewrite addZeroRight b | additionZeroDoesNothing (negSucc x +Z nonneg b) = refl
    addNonnegThenNonneg (negSucc x) b (succ c) with addNonnegThenNonneg (negSucc x) b c
    ... | prev = prev'
      where
        prev' : ((negSucc x +Z nonneg b) +Z nonneg (succ c)) ≡ negSucc x +Z nonneg (b +N succ c)
        prev' rewrite addNonnegSucc' (negSucc x +Z nonneg b) (negSucc x) c (b +N c) prev | succExtracts b c = refl

    additionZIsAssociativeFirstAndSecondArgNonneg : (a b : ℕ) (c : ℤ) → (nonneg a +Z (nonneg b +Z c)) ≡ ((nonneg a) +Z nonneg b) +Z c
    additionZIsAssociativeFirstAndSecondArgNonneg zero b c = refl
    additionZIsAssociativeFirstAndSecondArgNonneg (succ a) b (nonneg zero) = i
      where
        h : nonneg (succ a) +Z (nonneg b +Z nonneg zero) ≡ nonneg (succ a) +Z nonneg b
        h = identityOfIndiscernablesLeft (nonneg (succ a) +Z nonneg b) (nonneg (succ a) +Z nonneg b) (nonneg (succ a) +Z (nonneg b +Z nonneg zero)) _≡_ refl (applyEquality (λ r → nonneg (succ a) +Z r) {nonneg b} {nonneg b +Z nonneg zero} (equalityCommutative (additionZeroDoesNothing (nonneg b))))
        i : nonneg (succ a) +Z (nonneg b +Z nonneg zero) ≡ (nonneg (succ a) +Z nonneg b) +Z nonneg zero
        i = identityOfIndiscernablesRight (nonneg (succ a) +Z (nonneg b +Z nonneg zero)) (nonneg (succ a) +Z nonneg b) ((nonneg (succ a) +Z nonneg b) +Z nonneg zero) _≡_ h (equalityCommutative (additionZeroDoesNothing (nonneg (succ a) +Z nonneg b)))
    additionZIsAssociativeFirstAndSecondArgNonneg (succ x) zero (nonneg (succ c)) = applyEquality nonneg (applyEquality succ (applyEquality (λ n → n +N succ c) {x} {x +N zero} (equalityCommutative (addZeroRight x))))
    additionZIsAssociativeFirstAndSecondArgNonneg (succ x) (succ b) (nonneg (succ c)) = applyEquality nonneg (applyEquality succ i)
      where
        h : x +N (succ b +N succ c) ≡ (x +N succ b) +N succ c
        h = equalityCommutative (additionNIsAssociative x (succ b) (succ c))
        i : x +N succ (b +N succ c) ≡ (x +N succ b) +N succ c
        i = identityOfIndiscernablesLeft (x +N (succ b +N succ c)) ((x +N succ b) +N succ c) (x +N succ (b +N succ c)) _≡_ h refl
    additionZIsAssociativeFirstAndSecondArgNonneg (succ x) zero (negSucc c) rewrite addZeroRight x = refl
    additionZIsAssociativeFirstAndSecondArgNonneg (succ x) (succ b) (negSucc zero) rewrite additionNIsCommutative x b | additionNIsCommutative x (succ b) = refl
    additionZIsAssociativeFirstAndSecondArgNonneg (succ x) (succ b) (negSucc (succ c)) rewrite additionNIsCommutative x (succ b) | additionNIsCommutative b x = additionZIsAssociativeFirstAndSecondArgNonneg (succ x) b (negSucc c)

    additionZIsAssociativeFirstArgNonneg : (a : ℕ) (b c : ℤ) → (nonneg a +Z (b +Z c) ≡ ((nonneg a) +Z b) +Z c)
    additionZIsAssociativeFirstArgNonneg zero (nonneg b) c = additionZIsAssociativeFirstAndSecondArgNonneg 0 b c
    additionZIsAssociativeFirstArgNonneg 0 (negSucc b) c = refl
    additionZIsAssociativeFirstArgNonneg (succ a) (nonneg b) c = additionZIsAssociativeFirstAndSecondArgNonneg (succ a) b c
    additionZIsAssociativeFirstArgNonneg (succ x) (negSucc zero) (nonneg 0) rewrite addingNonnegIsHom x zero | addZeroRight x = refl
    additionZIsAssociativeFirstArgNonneg (succ x) (negSucc zero) (nonneg (succ c)) = i
      where
        h : nonneg (succ (x +N c)) ≡ nonneg (x +N succ c)
        s : nonneg (x +N succ c) ≡ nonneg (succ c +N x)
        t : nonneg (x +N succ c) ≡ nonneg (succ c) +Z nonneg x
        i : nonneg (succ (x +N c)) ≡ nonneg x +Z nonneg (succ c)
        h = applyEquality nonneg (equalityCommutative (succExtracts x c))
        s = applyEquality nonneg (additionNIsCommutative x (succ c))
        t = transitivity s refl
        i = transitivity h (equalityCommutative (addingNonnegIsHom x (succ c)))
    additionZIsAssociativeFirstArgNonneg (succ x) (negSucc (succ b)) (nonneg 0) rewrite additionZIsCommutative (nonneg x +Z negSucc b) (nonneg zero) = refl
    additionZIsAssociativeFirstArgNonneg (succ x) (negSucc (succ b)) (nonneg (succ c)) = p
      where
        p''' : nonneg x +Z (negSucc b +Z nonneg c) ≡ (nonneg x +Z negSucc b) +Z nonneg c
        p''' = additionZIsAssociativeFirstArgNonneg x (negSucc b) (nonneg c)
        p'' : (negSucc b +Z nonneg c) +Z nonneg x ≡ (nonneg x +Z negSucc b) +Z nonneg c
        p'' = identityOfIndiscernablesLeft (nonneg x +Z (negSucc b +Z nonneg c)) ((nonneg x +Z negSucc b) +Z nonneg c) ((negSucc b +Z nonneg c) +Z nonneg x) _≡_ p''' (additionZIsCommutative (nonneg x) (negSucc b +Z nonneg c))
        p' : (negSucc b +Z nonneg c) +Z nonneg (succ x) ≡ (nonneg x +Z negSucc b) +Z nonneg (succ c)
        p' = addNonnegSucc' (negSucc b +Z nonneg c) (nonneg x +Z negSucc b) x c p''
        p : nonneg (succ x) +Z (negSucc b +Z nonneg c) ≡ (nonneg x +Z negSucc b) +Z nonneg (succ c)
        p = identityOfIndiscernablesLeft ((negSucc b +Z nonneg c) +Z nonneg (succ x)) ((nonneg x +Z negSucc b) +Z nonneg (succ c)) (nonneg (succ x) +Z (negSucc b +Z nonneg c)) _≡_ p' (additionZIsCommutative (negSucc b +Z nonneg c) (nonneg (succ x)))
    additionZIsAssociativeFirstArgNonneg (succ x) (negSucc zero) (negSucc c) = refl
    additionZIsAssociativeFirstArgNonneg (succ a) (negSucc (succ b)) (negSucc zero) rewrite additionNIsCommutative b 1 | additionZIsCommutative (nonneg a +Z negSucc b) (negSucc 0) = equalityCommutative (moveNegsuccConverse 0 (nonneg a +Z negSucc b) (nonneg a +Z negSucc (succ b)) q'')
      where
        q : nonneg 1 +Z (nonneg a +Z negSucc (succ b)) ≡ (nonneg 1 +Z nonneg a) +Z negSucc (succ b)
        q = additionZIsAssociativeFirstAndSecondArgNonneg 1 a (negSucc (succ b))
        q' : (nonneg 1 +Z nonneg a) +Z negSucc (succ b) ≡ (nonneg a +Z negSucc (succ b)) +Z nonneg 1
        q' rewrite additionZIsCommutative (nonneg a +Z negSucc (succ b)) (nonneg 1) = equalityCommutative q
        q'' : nonneg (succ a) +Z negSucc (succ b) ≡ (nonneg a +Z negSucc (succ b)) +Z nonneg 1
        q'' rewrite addingNonnegIsHom 1 a = q'
    additionZIsAssociativeFirstArgNonneg (succ a) (negSucc (succ b)) (negSucc (succ c)) = ans
      where
        ans : nonneg a +Z negSucc (b +N succ (succ c)) ≡ (nonneg a +Z negSucc b) +Z negSucc (succ c)
        p :   nonneg a +Z (negSucc b +Z negSucc (succ c)) ≡ (nonneg a +Z negSucc b) +Z negSucc (succ c)
        p = additionZIsAssociativeFirstArgNonneg a (negSucc b) (negSucc (succ c))
        p' : negSucc (b +N succ (succ c)) ≡ negSucc b +Z negSucc (succ c)
        p' rewrite additionZIsCommutative (negSucc b) (negSucc (succ c)) | additionNIsCommutative b (succ (succ c)) | additionNIsCommutative c (succ b) | additionNIsCommutative c b  = refl
        ans rewrite p' = p

    additionZIsAssociative : (a b c : ℤ) → (a +Z (b +Z c)) ≡ (a +Z b) +Z c
    additionZIsAssociative (nonneg a) b c = additionZIsAssociativeFirstArgNonneg a b c
    additionZIsAssociative (negSucc a) (nonneg b) c rewrite additionZIsCommutative (negSucc a) (nonneg b) | additionZIsCommutative (negSucc a) (nonneg b +Z c) = p''
      where
        p : (nonneg b +Z c) +Z negSucc a ≡ nonneg b +Z (c +Z negSucc a)
        p = equalityCommutative (additionZIsAssociativeFirstArgNonneg b c (negSucc a))
        p' : (nonneg b +Z c) +Z negSucc a ≡ nonneg b +Z (negSucc a +Z c)
        p' rewrite additionZIsCommutative (negSucc a) c = p
        p'' : (nonneg b +Z c) +Z negSucc a ≡ (nonneg b +Z negSucc a) +Z c
        p'' rewrite equalityCommutative (additionZIsAssociativeFirstArgNonneg b (negSucc a) c) = p'
    additionZIsAssociative (negSucc a) (negSucc b) (nonneg c) rewrite additionZIsCommutative (negSucc a +Z negSucc b) (nonneg c) | additionZIsCommutative (negSucc b) (nonneg c) | additionZIsCommutative (negSucc a) (nonneg c +Z negSucc b) = p'
      where
        p : (nonneg c +Z negSucc b) +Z negSucc a ≡ nonneg c +Z (negSucc b +Z negSucc a)
        p = equalityCommutative (additionZIsAssociativeFirstArgNonneg c (negSucc b) (negSucc a))
        p' : (nonneg c +Z negSucc b) +Z negSucc a ≡ nonneg c +Z (negSucc a +Z negSucc b)
        p' rewrite additionZIsCommutative (negSucc a) (negSucc b) = p
    additionZIsAssociative (negSucc zero) (negSucc zero) (negSucc c) = refl
    additionZIsAssociative (negSucc zero) (negSucc (succ b)) (negSucc c) = refl
    additionZIsAssociative (negSucc (succ a)) (negSucc zero) (negSucc c) rewrite additionNIsCommutative a 1 | additionNIsCommutative a (succ (succ c)) | additionNIsCommutative a (succ c) = refl
    additionZIsAssociative (negSucc (succ a)) (negSucc (succ b)) (negSucc zero) rewrite additionNIsCommutative b 1 | additionNIsCommutative (succ ((a +N succ (succ b)))) 1 = applyEquality (λ t → negSucc (succ t)) (p (succ (succ b)))
      where
        p : (r : ℕ) → a +N succ r ≡ succ (a +N r)
        p r rewrite additionNIsCommutative a (succ r) | additionNIsCommutative r a = refl
    additionZIsAssociative (negSucc (succ a)) (negSucc (succ b)) (negSucc (succ c)) = applyEquality (λ t → negSucc (succ t)) (equalityCommutative (additionNIsAssociative a (succ (succ b)) (succ (succ c))))

    lessZIrreflexive : {a : ℤ} → (a <Z a) → False
    lessZIrreflexive {nonneg a} (le x proof) = lessLemma a x (nonnegInjective proof)
    lessZIrreflexive {negSucc a} (le x proof) = naughtE (equalityCommutative q)
      where
        pr' : nonneg (succ x) +Z (negSucc a +Z nonneg (succ a)) ≡ negSucc a +Z nonneg (succ a)
        pr' rewrite additionZIsAssociative (nonneg (succ x)) (negSucc a) (nonneg (succ a)) = applyEquality (λ t → t +Z nonneg (succ a)) proof
        pr'' : nonneg (succ x) +Z nonneg 0 ≡ nonneg 0
        pr'' rewrite equalityCommutative (additiveInverseExists a) = identityOfIndiscernablesLeft (nonneg (succ x) +Z (negSucc a +Z nonneg (succ a))) (negSucc a +Z nonneg (succ a)) (nonneg (succ (x +N zero))) _≡_ pr' q
          where
            q : nonneg (succ x) +Z (negSucc a +Z nonneg (succ a)) ≡ nonneg (succ (x +N 0))
            q rewrite additionNIsCommutative x 0 | additiveInverseExists a | additionNIsCommutative x 0 = refl
        pr''' : succ x +N 0 ≡ 0
        pr''' rewrite addingNonnegIsHom (succ x) 0 = nonnegInjective pr''
        q : succ x ≡ 0
        q rewrite additionNIsCommutative 0 (succ x) = pr'''

    lessNegsuccNonneg : {a b : ℕ} → (negSucc a <Z nonneg b)
    lessNegsuccNonneg {a} {b} = record { x = x ; proof = pr }
      where
        x : ℕ
        x = a +N b
        pr' : nonneg (succ (a +N b)) ≡ nonneg b +Z nonneg (succ a)
        pr' rewrite addingNonnegIsHom b (succ a) | additionNIsCommutative b (succ a) = refl
        pr : nonneg (succ x) +Z negSucc a ≡ nonneg b
        pr rewrite additionZIsCommutative (nonneg (succ x)) (negSucc a) = moveNegsuccConverse a (nonneg (succ (a +N b))) (nonneg b) pr'

    lessThanTotalZ : {a b : ℤ} → ((a <Z b) || (b <Z a)) || (a ≡ b)
    lessThanTotalZ {nonneg a} {nonneg b} with orderIsTotal a b
    lessThanTotalZ {nonneg a} {nonneg b} | inl (inl a<b) = inl (inl (lessIsPreservedNToZ a<b))
    lessThanTotalZ {nonneg a} {nonneg b} | inl (inr b<a) = inl (inr (lessIsPreservedNToZ b<a))
    lessThanTotalZ {nonneg a} {nonneg b} | inr a=b = inr (applyEquality nonneg a=b)
    lessThanTotalZ {nonneg a} {negSucc b} = inl (inr (lessNegsuccNonneg {b} {a}))
    lessThanTotalZ {negSucc a} {nonneg x} = inl (inl (lessNegsuccNonneg {a} {x}))
    lessThanTotalZ {negSucc a} {negSucc b} with orderIsTotal a b
    ... | inl (inl a<b) = inl (inr (lessIsPreservedNToZNegsucc a<b))
    ... | inl (inr b<a) = inl (inl (lessIsPreservedNToZNegsucc b<a))
    lessThanTotalZ {negSucc a} {negSucc .a} | inr refl = inr refl

    negSuccPlusNegsuccIsNegsucc : {a b c : ℕ} → (negSucc a +Z negSucc b ≡ nonneg c) → False
    negSuccPlusNegsuccIsNegsucc {zero} {b} {c} pr = nonnegIsNotNegsucc (equalityCommutative pr)
    negSuccPlusNegsuccIsNegsucc {succ a} {b} {c} pr = nonnegIsNotNegsucc (equalityCommutative pr)

    multiplicationZ'IsAssociative : (a b c : ℤSimple) → (a *Z' (b *Z' c)) ≡ ((a *Z' b) *Z' c)
    multiplicationZ'IsAssociative (negative zero (le x ())) b c
    multiplicationZ'IsAssociative (negative (succ a) x) (negative zero (le x₁ ())) c
    multiplicationZ'IsAssociative (negative (succ a) x) (negative (succ b) prb) (negative zero (le x₁ ()))
    multiplicationZ'IsAssociative (negative (succ a) x) (negative ( succ b) prb) (negative (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → negative (succ a *N (succ b *N succ c)) pr1 ≡ negative ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = negIsNeg pr1 pr2
    multiplicationZ'IsAssociative (negative (succ a) x) (negative (succ b) prb) (positive zero (le x₁ ()))
    multiplicationZ'IsAssociative (negative (succ a) x) (negative (succ b) prb) (positive (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → positive (succ a *N (succ b *N succ c)) pr1 ≡ positive ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = posIsPos pr1 pr2
    multiplicationZ'IsAssociative (negative (succ a) x) (negative (succ b) prb) zZero = refl
    multiplicationZ'IsAssociative (negative (succ a) x) (positive zero (le x₁ ())) c
    multiplicationZ'IsAssociative (negative (succ a) x) (positive (succ b) prb) (negative zero (le x₁ ()))
    multiplicationZ'IsAssociative (negative (succ a) x) (positive (succ b) prb) (negative (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → positive (succ a *N (succ b *N succ c)) pr1 ≡ positive ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = posIsPos pr1 pr2
    multiplicationZ'IsAssociative (negative (succ a) x) (positive (succ b) prb) (positive zero (le x₁ ()))
    multiplicationZ'IsAssociative (negative (succ a) x) (positive (succ b) prb) (positive (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → negative (succ a *N (succ b *N succ c)) pr1 ≡ negative ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = negIsNeg pr1 pr2
    multiplicationZ'IsAssociative (negative (succ a) x) (positive (succ b) prb) zZero = refl
    multiplicationZ'IsAssociative (negative (succ a) x) zZero c = refl
    multiplicationZ'IsAssociative (positive zero (le x ())) b c
    multiplicationZ'IsAssociative (positive (succ a) x) (negative zero (le y ())) c
    multiplicationZ'IsAssociative (positive (succ a) x) (negative (succ b) prb) (negative zero (le x₁ ()))
    multiplicationZ'IsAssociative (positive (succ a) x) (negative (succ b) prb) (negative (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → positive (succ a *N (succ b *N succ c)) pr1 ≡ positive ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = posIsPos pr1 pr2
    multiplicationZ'IsAssociative (positive (succ a) x) (negative (succ b) prb) (positive zero (le x₁ ()))
    multiplicationZ'IsAssociative (positive (succ a) x) (negative (succ b) prb) (positive (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → negative (succ a *N (succ b *N succ c)) pr1 ≡ negative ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = negIsNeg pr1 pr2
    multiplicationZ'IsAssociative (positive (succ a) x) (negative (succ b) prb) zZero = refl
    multiplicationZ'IsAssociative (positive (succ a) x) (positive zero (le y ())) c
    multiplicationZ'IsAssociative (positive (succ a) x) (positive (succ b) prb) (negative zero (le x₁ ()))
    multiplicationZ'IsAssociative (positive (succ a) x) (positive (succ b) prb) (negative (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → negative (succ a *N (succ b *N succ c)) pr1 ≡ negative ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = negIsNeg pr1 pr2
    multiplicationZ'IsAssociative (positive (succ a) x) (positive (succ b) prb) (positive zero (le x₁ ()))
    multiplicationZ'IsAssociative (positive (succ a) x) (positive (succ b) prb) (positive (succ c) prc) = res _ _
      where
        help : _
        help = multiplicationNIsAssociative (succ a) (succ b) (succ c)
        res : (pr1 : 0 <N succ a *N (succ b *N succ c)) → (pr2 : 0 <N (succ a *N succ b) *N succ c) → positive (succ a *N (succ b *N succ c)) pr1 ≡ positive ((succ a *N succ b) *N succ c) pr2
        res pr1 pr2 rewrite help = posIsPos pr1 pr2
    multiplicationZ'IsAssociative (positive (succ a) x) (positive (succ b) prb) zZero = refl
    multiplicationZ'IsAssociative (positive (succ a) x) zZero c = refl
    multiplicationZ'IsAssociative zZero b c = refl

    multiplicationZIsAssociative : (a b c : ℤ) → (a *Z (b *Z c)) ≡ (a *Z b) *Z c
    multiplicationZIsAssociative a b c = ans
      where
        inter : convertZ' (convertZ a *Z' (convertZ b *Z' convertZ c)) ≡ convertZ' ((convertZ a *Z' convertZ b) *Z' convertZ c)
        inter = applyEquality convertZ' (multiplicationZ'IsAssociative (convertZ a) (convertZ b) (convertZ c))
        ans : a *Z (b *Z c) ≡ (a *Z b) *Z c
        ans rewrite convertZ'DistributesOver*Z (convertZ a) (convertZ b *Z' convertZ c) | convertZ'DistributesOver*Z (convertZ b) (convertZ c) | convertZ'DistributesOver*Z (convertZ a *Z' convertZ b) (convertZ c) | convertZ'DistributesOver*Z (convertZ a) (convertZ b) | zIsZ c | zIsZ b | zIsZ a | zIsZ' (convertZ b *Z' convertZ c) | zIsZ' (convertZ a *Z' convertZ b) = inter

    zeroIsAdditiveIdentityRightZ : (a : ℤ) → (a +Z nonneg zero) ≡ a
    zeroIsAdditiveIdentityRightZ (nonneg x) = identityOfIndiscernablesRight (nonneg x +Z nonneg zero) (nonneg (x +N zero)) (nonneg x) _≡_ (addingNonnegIsHom x zero) ((applyEquality nonneg (addZeroRight x)))
    zeroIsAdditiveIdentityRightZ (negSucc a) = refl

    additiveInverseZ : (a : ℤ) → ℤ
    additiveInverseZ (nonneg zero) = nonneg zero
    additiveInverseZ (nonneg (succ x)) = negSucc x
    additiveInverseZ (negSucc a) = nonneg (succ a)

    addInverseLeftZ : (a : ℤ) → (additiveInverseZ a +Z a ≡ nonneg zero)
    addInverseLeftZ (nonneg zero) = refl
    addInverseLeftZ (nonneg (succ zero)) = refl
    addInverseLeftZ (nonneg (succ (succ x))) = addInverseLeftZ (nonneg (succ x))
    addInverseLeftZ (negSucc zero) = refl
    addInverseLeftZ (negSucc (succ a)) = addInverseLeftZ (negSucc a)

    addInverseRightZ : (a : ℤ) → (a +Z additiveInverseZ a ≡ nonneg zero)
    addInverseRightZ (nonneg zero) = refl
    addInverseRightZ (nonneg (succ zero)) = refl
    addInverseRightZ (nonneg (succ (succ x))) = addInverseRightZ (nonneg (succ x))
    addInverseRightZ (negSucc zero) = refl
    addInverseRightZ (negSucc (succ a)) = addInverseRightZ (negSucc a)

    flipSign : (a : ℕ) → negSucc a *Z negSucc 0 ≡ nonneg (succ a)
    flipSign zero = refl
    flipSign (succ a) = ans
      where
        help : convertZ (negSucc (succ a)) *Z' convertZ (negSucc 0) ≡ convertZ (nonneg (succ (succ a)))
        help rewrite multiplicationNIsCommutative a 1 | additionNIsCommutative a 0 = refl
        help' : convertZ' (convertZ (negSucc (succ a)) *Z' convertZ (negSucc 0)) ≡ convertZ' (convertZ (nonneg (succ (succ a))))
        help' = applyEquality convertZ' help
        help'' : convertZ' (convertZ (negSucc (succ a))) *Z (convertZ' (convertZ (negSucc 0))) ≡ nonneg (succ (succ a))
        help'' rewrite convertZ'DistributesOver*Z (convertZ (negSucc (succ a))) (convertZ (negSucc 0)) | zIsZ (nonneg (succ (succ a))) = help'
        ans : negSucc (succ a) *Z negSucc 0 ≡ nonneg (succ (succ a))
        ans rewrite zIsZ (negSucc (succ a)) | zIsZ (negSucc 0) = help''

    flipSign' : (a : ℕ) → nonneg (succ a) *Z negSucc 0 ≡ negSucc a
    flipSign' a = ans
      where
        inter : negSucc 0 *Z negSucc 0 ≡ nonneg 1
        inter = refl
        ans : nonneg (succ a) *Z negSucc 0 ≡ negSucc a
        ans rewrite inter | multiplicationNIsCommutative a 1 | additionNIsCommutative a 0 = refl

    additionZ'IsCommutative : (a b : ℤSimple) → a +Z' b ≡ b +Z' a
    additionZ'IsCommutative a b = ans
      where
        help : (convertZ' a) +Z (convertZ' b) ≡ (convertZ' b) +Z (convertZ' a)
        help = additionZIsCommutative (convertZ' a) (convertZ' b)
        help' : convertZ ((convertZ' a) +Z (convertZ' b)) ≡ convertZ ((convertZ' b) +Z (convertZ' a))
        help' = applyEquality convertZ help
        help'' : convertZ (convertZ' a) +Z' convertZ (convertZ' b) ≡ convertZ (convertZ' b) +Z' convertZ (convertZ' a)
        help'' rewrite equalityCommutative (plusIsPlus' (convertZ' a) (convertZ' b)) | equalityCommutative (plusIsPlus' (convertZ' b) (convertZ' a)) = help'
        ans : a +Z' b ≡ b +Z' a
        ans rewrite equalityCommutative (zIsZ' a) | equalityCommutative (zIsZ' b) = help''
    additionZ'IsAssociative : (a b c : ℤSimple) → (a +Z' (b +Z' c)) ≡ (a +Z' b) +Z' c
    additionZ'IsAssociative a b c = identityOfIndiscernablesRight _ _ _ _≡_ helpV''' (applyEquality (λ t → (a +Z' t) +Z' c) (zIsZ' b))
      where
        help  : convertZ (convertZ' a +Z (convertZ' b +Z convertZ' c)) ≡ convertZ ((convertZ' a +Z convertZ' b) +Z convertZ' c)
        help' : convertZ (convertZ' a) +Z' convertZ (convertZ' b +Z convertZ' c) ≡ convertZ (convertZ' a +Z convertZ' b) +Z' convertZ (convertZ' c)
        help'' : a +Z' convertZ (convertZ' b +Z convertZ' c) ≡ convertZ (convertZ' a +Z convertZ' b) +Z' convertZ (convertZ' c)
        help''' : a +Z' (convertZ (convertZ' b) +Z' convertZ (convertZ' c)) ≡ convertZ (convertZ' a +Z convertZ' b) +Z' convertZ (convertZ' c)
        help'''' : a +Z' (b +Z' (convertZ (convertZ' c))) ≡ convertZ (convertZ' a +Z convertZ' b) +Z' convertZ (convertZ' c)
        helpV : a +Z' (b +Z' c) ≡ convertZ (convertZ' a +Z convertZ' b) +Z' convertZ (convertZ' c)
        helpV' : a +Z' (b +Z' c) ≡ convertZ (convertZ' a +Z convertZ' b) +Z' c
        helpV'' : a +Z' (b +Z' c) ≡ (convertZ (convertZ' a) +Z' convertZ (convertZ' b)) +Z' c
        helpV''' : a +Z' (b +Z' c) ≡ (a +Z' convertZ (convertZ' b)) +Z' c
        helpV''' = identityOfIndiscernablesRight _ _ _ _≡_ helpV'' (applyEquality (λ t → ((t +Z' convertZ (convertZ' b)) +Z' c)) (zIsZ' a))
        helpV'' rewrite equalityCommutative (plusIsPlus' (convertZ' a) (convertZ' b)) = helpV'
        helpV' = identityOfIndiscernablesRight _ _ _ _≡_ helpV (applyEquality (λ t → convertZ (convertZ' a +Z convertZ' b) +Z' t) (zIsZ' c))
        helpV = identityOfIndiscernablesLeft _ _ _ _≡_ help'''' (applyEquality (λ t → a +Z' (b +Z' t)) (zIsZ' c))
        help'''' = identityOfIndiscernablesLeft _ _ _ _≡_ help''' (applyEquality (λ t → a +Z' (t +Z' (convertZ (convertZ' c)))) (zIsZ' b))
        help''' rewrite equalityCommutative (plusIsPlus' (convertZ' b) (convertZ' c)) = help''
        help'' = identityOfIndiscernablesLeft (convertZ (convertZ' a) +Z' convertZ (convertZ' b +Z convertZ' c)) _ (a +Z' convertZ (convertZ' b +Z convertZ' c)) _≡_ help' (applyEquality (λ t → t +Z' convertZ (convertZ' b +Z convertZ' c)) (zIsZ' a))
        help = applyEquality convertZ (additionZIsAssociative (convertZ' a) (convertZ' b) (convertZ' c))
        help' rewrite equalityCommutative (plusIsPlus' (convertZ' a) (convertZ' b +Z convertZ' c)) | equalityCommutative (plusIsPlus' (convertZ' a +Z convertZ' b) (convertZ' c)) = help

    pos+Z'Pos : (a b : ℕ) → {pr : 0 <N a} → {pr2 : 0 <N b} → {pr3 : 0 <N a +N b} → (positive a pr) +Z' (positive b pr2) ≡ positive (a +N b) pr3
    pos+Z'Pos zero b {le x ()} {pr2} {pr3}
    pos+Z'Pos (succ a) zero {pr} {le x ()} {pr3}
    pos+Z'Pos (succ a) (succ b) {pr} {pr2} {pr3} rewrite <NRefl (pr) (succIsPositive a) | <NRefl pr2 (succIsPositive b) | <NRefl pr3 (succIsPositive (a +N succ b)) = refl

    lemma'' : (a b c : ℕ) → (pr : _) → (pr2 : _) → (pr3 : _) → positive (succ ((b +N succ c) +N a *N succ (b +N succ c))) pr ≡ positive (succ (b +N a *N succ b)) pr2 +Z' positive (succ (c +N a *N succ c)) pr3
    lemma'' a b c pr1 pr2 pr3 = equalityCommutative help'
      where
        pr' : succ (b +N a *N succ b) +N succ (c +N a *N succ c) ≡ succ ((b +N succ c) +N a *N succ (b +N succ c))
        pr' = equalityCommutative (productDistributes (succ a) (succ b) (succ c))
        pr'' : 0 <N succ (b +N a *N succ b) +N succ (c +N a *N succ c)
        pr'' rewrite pr' = pr1
        help : (positive (succ (b +N a *N succ b))) pr2 +Z' (positive (succ (c +N a *N succ c))) pr3 ≡ positive (succ (b +N a *N succ b) +N succ (c +N a *N succ c)) pr''
        help = pos+Z'Pos (succ (b +N a *N succ b)) (succ (c +N a *N succ c)) {pr2} {pr3} {pr''}
        help' : (positive (succ (b +N a *N succ b))) pr2 +Z' (positive (succ (c +N a *N succ c))) pr3 ≡ positive (succ ((b +N succ c) +N a *N succ (b +N succ c))) pr1
        help' rewrite equalityCommutative pr' | <NRefl pr1 (succIsPositive ((b +N a *N succ b) +N succ (c +N a *N succ c))) = refl

    addZZero : (a : ℤSimple) → a +Z' zZero ≡ a
    addZZero (negative zero (le x ()))
    addZZero (negative (succ a) x) rewrite additionZ'IsCommutative (negative (succ a) x) zZero = refl
    addZZero (positive zero (le x ()))
    addZZero (positive (succ a) x) rewrite additionZ'IsCommutative (positive (succ a) x) zZero = refl
    addZZero zZero = refl

    negSucc+ZNegSucc : (a b : ℕ) → (negSucc a +Z negSucc b) ≡ negSucc (succ a +N b)
    negSucc+ZNegSucc zero b = refl
    negSucc+ZNegSucc (succ a) b rewrite additionNIsCommutative a (succ b) | additionNIsCommutative b a = refl

    oneIsIdentity : (a : ℤ) → convertZ' (positive 1 (succIsPositive 0) *Z' convertZ a) ≡ a
    oneIsIdentity (nonneg zero) = refl
    oneIsIdentity (nonneg (succ x)) rewrite additionNIsCommutative x 0 = refl
    oneIsIdentity (negSucc x) rewrite additionNIsCommutative x 0 = refl

    oneIsIdentity' : (a : ℤSimple) → (positive 1 (succIsPositive 0)) *Z' a ≡ a
    oneIsIdentity' (negative zero (le x ()))
    oneIsIdentity' (negative (succ a) x) rewrite additionNIsCommutative a 0 | <NRefl x (logical<NImpliesLe (record {})) = refl
    oneIsIdentity' (positive zero (le x ()))
    oneIsIdentity' (positive (succ a) x) rewrite additionNIsCommutative a 0 | <NRefl x (logical<NImpliesLe (record {})) = refl
    oneIsIdentity' zZero = refl

    canPullOutSuccZ' : (a : ℕ) → (b c : ℤSimple) → (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ (b +Z' c) +Z' (positive (succ a) (succIsPositive a)) *Z' (b +Z' c)
    canPullOutSuccZ' a (negative zero (le x ())) c
    canPullOutSuccZ' a (negative (succ b) _) (negative zero (le x ()))
    canPullOutSuccZ' a (negative (succ b) _) (negative (succ c) x) = refl
    canPullOutSuccZ' a (negative (succ b) _) (positive zero (le x ()))
    canPullOutSuccZ' a (negative (succ b) y) (positive (succ c) x) with negative (succ b) y +Z' positive (succ c) x
    canPullOutSuccZ' a (negative (succ b) y) (positive (succ c) x) | negative zero (le x₁ ())
    canPullOutSuccZ' a (negative (succ b) y) (positive (succ c) x) | negative (succ sum) pr = refl
    canPullOutSuccZ' a (negative (succ b) y) (positive (succ c) x) | positive zero (le x₁ ())
    canPullOutSuccZ' a (negative (succ b) y) (positive (succ c) x) | positive (succ sum) pr = refl
    canPullOutSuccZ' a (negative (succ b) y) (positive (succ c) x) | zZero = refl
    canPullOutSuccZ' a (negative (succ b) _) zZero = refl
    canPullOutSuccZ' a (positive zero (le x ())) c
    canPullOutSuccZ' a (positive (succ b) _) (negative zero (le x ()))
    canPullOutSuccZ' a (positive (succ b) y) (negative (succ c) x) with positive (succ b) y +Z' negative (succ c) x
    canPullOutSuccZ' a (positive (succ b) y) (negative (succ c) x) | negative zero (le x₁ ())
    canPullOutSuccZ' a (positive (succ b) y) (negative (succ c) x) | negative (succ sum) pr = refl
    canPullOutSuccZ' a (positive (succ b) y) (negative (succ c) x) | positive zero (le x₁ ())
    canPullOutSuccZ' a (positive (succ b) y) (negative (succ c) x) | positive (succ sum) pr = refl
    canPullOutSuccZ' a (positive (succ b) y) (negative (succ c) x) | zZero = refl
    canPullOutSuccZ' a (positive (succ b) _) (positive zero (le x ()))
    canPullOutSuccZ' a (positive (succ b) _) (positive (succ c) x) = refl
    canPullOutSuccZ' a (positive (succ b) _) zZero = refl
    canPullOutSuccZ' a zZero (negative zero (le x ()))
    canPullOutSuccZ' a zZero (negative (succ c) x) = refl
    canPullOutSuccZ' a zZero (positive zero (le x ()))
    canPullOutSuccZ' a zZero (positive (succ c) x) = refl
    canPullOutSuccZ' a zZero zZero = refl

    canPullOutSuccZ : (a : ℕ) → (b : ℤSimple) → (positive (succ (succ a)) (succIsPositive (succ a))) *Z' b ≡ b +Z' (positive (succ a) (succIsPositive a)) *Z' b
    canPullOutSuccZ a b = ans b
      where
        ans : (b : ℤSimple) → (positive (succ (succ a)) (succIsPositive (succ a))) *Z' b ≡ b +Z' (positive (succ a) (succIsPositive a)) *Z' b
        ans (negative zero (le x ()))
        ans (negative (succ b) x) = refl
        ans (positive zero (le x ()))
        ans (positive (succ b) x) = refl
        ans zZero = refl


    swapAdds : (a c : ℕ) → (a +N succ c) +N succ (a +N succ c) ≡ (a +N succ a) +N succ (c +N succ c)
    swapAdds a c rewrite additionNIsAssociative a (succ c) (succ (a +N succ c)) | additionNIsAssociative a (succ a) (succ (c +N succ c)) = applyEquality (λ t → a +N succ t) help'
      where
        help' : c +N succ (a +N succ c) ≡ a +N succ (c +N succ c)
        help' rewrite additionNIsCommutative c (succ (a +N succ c)) | additionNIsCommutative (a +N succ c) c | additionNIsCommutative (succ c) (a +N succ c) | additionNIsAssociative a (succ c) (succ c) = refl

    lemmaDistributive : (a : ℕ) → (b c : ℤSimple) → (positive (succ a) (succIsPositive a)) *Z' (b +Z' c) ≡ positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c
    lemmaDistributive zero (negative zero (le x ())) c
    lemmaDistributive zero (negative (succ b) prB) (negative zero (le x ()))
    lemmaDistributive zero (negative (succ b) prB) (negative (succ a) x) rewrite additionNIsCommutative a 0 | additionNIsCommutative b 0 | additionNIsCommutative (b +N succ a) 0 = refl

    lemmaDistributive zero (negative (succ b) prB) (positive zero (le x ()))
    lemmaDistributive zero (negative (succ b) prB) (positive (succ a) x) rewrite oneIsIdentity' (negative (succ b) prB +Z' positive (succ a) x) | additionNIsCommutative b 0 | additionNIsCommutative a 0 | <NRefl x (logical<NImpliesLe (record {})) | <NRefl prB (logical<NImpliesLe (record {})) = refl
    lemmaDistributive zero (negative (succ b) prB) zZero = refl
    lemmaDistributive zero (positive zero (le x ())) c
    lemmaDistributive zero (positive (succ b) prB) (negative zero (le x ()))
    lemmaDistributive zero (positive (succ b) prB) (negative (succ a) x) rewrite additionNIsCommutative b 0 | additionNIsCommutative a 0 | oneIsIdentity' (positive (succ b) prB +Z' negative (succ a) x) | <NRefl prB (logical<NImpliesLe (record {})) | <NRefl x (logical<NImpliesLe (record {})) = refl
    lemmaDistributive zero (positive (succ b) prB) (positive zero (le x ()))
    lemmaDistributive zero (positive (succ b) prB) (positive (succ a) x) rewrite additionNIsCommutative b 0 | additionNIsCommutative a 0 = help2 ((b +N succ a) +N 0) (b +N succ a) (applyEquality succ lem)
      where
        help2 : (a b : ℕ) → (pr : succ a ≡ succ b) → positive (succ a) (succIsPositive _) ≡ positive (succ b) (succIsPositive _)
        help2 a .a refl = refl
        lem : (b +N succ a) +N 0 ≡ b +N succ a
        lem rewrite additionNIsCommutative (b +N succ a) 0 = refl
    lemmaDistributive zero (positive (succ b) prB) zZero = refl
    lemmaDistributive zero zZero c rewrite oneIsIdentity' (zZero +Z' c) | oneIsIdentity' c = refl
    lemmaDistributive (succ a) b c = lemmV''
      where
        internallemma' : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ (b +Z' c) +Z' (positive (succ a) (succIsPositive a)) *Z' (b +Z' c)
        internallemma' = canPullOutSuccZ' a b c
        p : positive (succ (succ a)) (succIsPositive (succ a)) *Z' b ≡ b +Z' positive (succ a) (succIsPositive a) *Z' b
        p = canPullOutSuccZ a b
        q : positive (succ (succ a)) (succIsPositive (succ a)) *Z' c ≡ c +Z' positive (succ a) (succIsPositive a) *Z' c
        q = canPullOutSuccZ a c
        indHyp : (positive (succ a) (succIsPositive a)) *Z' (b +Z' c) ≡ positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c
        indHyp = lemmaDistributive a b c
        lemm : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ (b +Z' c) +Z' (positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c)
        lemm rewrite equalityCommutative indHyp = internallemma'
        lemm' : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ b +Z' (c +Z' ((positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c)))
        lemm' rewrite additionZ'IsAssociative b c (positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c) = lemm
        lemm'' : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ b +Z' (((positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c)) +Z' c)
        inter : ((positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c)) +Z' c ≡ positive (succ a) (succIsPositive a) *Z' b +Z' ((positive (succ a) (succIsPositive a) *Z' c) +Z' c)
        lemm''' : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ b +Z' (positive (succ a) (succIsPositive a) *Z' b +Z' ((positive (succ a) (succIsPositive a) *Z' c) +Z' c))
        lemm'''' : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ (b +Z' (positive (succ a) (succIsPositive a) *Z' b)) +Z' ((positive (succ a) (succIsPositive a) *Z' c) +Z' c)
        lemm'''' rewrite equalityCommutative (additionZ'IsAssociative b (positive (succ a) (succIsPositive a) *Z' b) ((positive (succ a) (succIsPositive a) *Z' c) +Z' c)) = lemm'''
        lemmV : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ (positive (succ (succ a)) (succIsPositive (succ a)) *Z' b) +Z' ((positive (succ a) (succIsPositive a) *Z' c) +Z' c)
        lemmV rewrite p = lemm''''
        lemmV' : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ (positive (succ (succ a)) (succIsPositive (succ a)) *Z' b) +Z' (c +Z' (positive (succ a) (succIsPositive a) *Z' c))
        lemmV' rewrite additionZ'IsCommutative c (positive (succ a) (succIsPositive a) *Z' c) = lemmV
        lemmV'' : (positive (succ (succ a)) (succIsPositive (succ a))) *Z' (b +Z' c) ≡ (positive (succ (succ a)) (succIsPositive (succ a)) *Z' b) +Z' (positive (succ (succ a)) (succIsPositive (succ a)) *Z' c)
        lemmV'' rewrite q = lemmV'
        lemm'' rewrite additionZ'IsCommutative ((positive (succ a) (succIsPositive a) *Z' b +Z' positive (succ a) (succIsPositive a) *Z' c)) c = lemm'
        inter = equalityCommutative (additionZ'IsAssociative (positive (succ a) (succIsPositive a) *Z' b) (positive (succ a) (succIsPositive a) *Z' c) c)
        lemm''' rewrite equalityCommutative inter = lemm''

    addIsZero : (a b : ℕ) → {pr1 : 0 <N a} → {pr2 : 0 <N b} → ((positive a pr1) +Z' (negative b pr2) ≡ zZero) → a ≡ b
    addIsZero zero b {le x ()} {pr2} pr
    addIsZero (succ a) zero {pr1} {le x ()} pr
    addIsZero (succ zero) (succ zero) {pr1} {pr2} pr = refl
    addIsZero (succ zero) (succ (succ b)) {pr1} {pr2} pr = exFalso (f pr)
      where
        f : (negative (succ b) (logical<NImpliesLe (record {})) ≡ zZero) → False
        f ()
    addIsZero (succ (succ a)) (succ zero) {pr1} {pr2} pr = exFalso (f pr)
      where
        f : (positive (succ a) (logical<NImpliesLe (record {})) ≡ zZero) → False
        f ()
    addIsZero (succ (succ a)) (succ (succ b)) {pr1} {pr2} pr = applyEquality succ (addIsZero (succ a) (succ b) {succIsPositive a} {succIsPositive b} p)
      where
        q : positive (succ (succ a)) pr1 +Z' negative (succ (succ b)) pr2 ≡ positive (succ a) (succIsPositive a) +Z' negative (succ b) (succIsPositive b)
        q = canKnockOneOff+Z' (succ a) (succ b) {succIsPositive a} {succIsPositive b} {pr1} {pr2}
        p : positive (succ a) (succIsPositive a) +Z' negative (succ b) (succIsPositive b) ≡ zZero
        p rewrite equalityCommutative q = pr

    addIsZero' : (a : ℕ) → (negative (succ a) (succIsPositive a)) +Z' (positive (succ a) (succIsPositive a)) ≡ zZero
    addIsZero' (zero) = refl
    addIsZero' (succ a) = transitivity q p
      where
        p : negative (succ a) (succIsPositive a) +Z' positive (succ a) (succIsPositive a) ≡ zZero
        p = addIsZero' a
        q : negative (succ (succ a)) (succIsPositive (succ a)) +Z' positive (succ (succ a)) (succIsPositive (succ a)) ≡ negative (succ a) (succIsPositive a) +Z' positive (succ a) (succIsPositive a)
        q = canKnockOneOff+Z'2 (succ a) (succ a) {succIsPositive a} {succIsPositive a} {succIsPositive (succ a)} {succIsPositive (succ a)}

    timesNegPosPos : (a b c : ℕ) → (negative (succ a) (succIsPositive a)) *Z' ((positive (succ b) (succIsPositive b)) +Z' (positive (succ c) (succIsPositive c))) ≡ (positive (succ a) (succIsPositive a)) *Z' ((negative (succ b) (succIsPositive b)) +Z' (negative (succ c) (succIsPositive c)))
    timesNegPosPos a b c = refl

    diffProof : (a b : ℕ) → (sum1 sum2 : ℕ) → (pr1 : succ a +N succ b ≡ sum1) → (pr2 : succ a +N succ b ≡ sum2) → (prSums : sum1 ≡ sum2) → plusZ' sum1 (negative (succ a) (succIsPositive a)) (positive (succ b) (succIsPositive b)) pr1 ≡ plusZ' sum2 (negative (succ a) (succIsPositive a)) (positive (succ b) (succIsPositive b)) pr2
    diffProof a b .(succ (a +N succ b)) .(succ (a +N succ b)) refl refl refl = refl

    diffProof' : (a b : ℕ) → (sum1 sum2 : ℕ) → (pr1 : succ a +N succ b ≡ sum1) → (pr2 : succ a +N succ b ≡ sum2) → (prSums : sum1 ≡ sum2) → plusZ' sum1 (positive (succ a) (succIsPositive a)) (negative (succ b) (succIsPositive b)) pr1 ≡ plusZ' sum2 (positive (succ a) (succIsPositive a)) (negative (succ b) (succIsPositive b)) pr2
    diffProof' a b .(succ (a +N succ b)) .(succ (a +N succ b)) refl refl refl = refl

    timesNegPosNeg : (a b c : ℕ) → (negative (succ a) (succIsPositive a)) *Z' ((positive (succ b) (succIsPositive b)) +Z' (negative (succ c) (succIsPositive c))) ≡ (positive (succ a) (succIsPositive a)) *Z' ((negative (succ b) (succIsPositive b)) +Z' (positive (succ c) (succIsPositive c)))
    timesNegPosNeg zero zero zero = refl
    timesNegPosNeg zero zero (succ c) = refl
    timesNegPosNeg zero (succ b) zero = refl
    timesNegPosNeg zero (succ b) (succ c) = identityOfIndiscernablesRight _ _ _ _≡_ ans'' (applyEquality (λ t → positive 1 _ *Z' t) (knocked'))
      where
        knocked : positive (succ (succ b)) (succIsPositive (succ b)) +Z' negative (succ (succ c)) (succIsPositive (succ c)) ≡ positive (succ b) _ +Z' negative (succ c) _
        knocked = canKnockOneOff+Z' (succ b) (succ c) {succIsPositive b} {succIsPositive c} {succIsPositive (succ b)} {succIsPositive (succ c)}
        knocked' : negative (succ b) (succIsPositive b) +Z' positive (succ c) (succIsPositive c) ≡ negative (succ (succ b)) (succIsPositive (succ b)) +Z' positive (succ (succ c)) (succIsPositive (succ c))
        knocked' rewrite additionZ'IsCommutative (negative (succ b) (succIsPositive b)) (positive (succ c) (succIsPositive c)) | additionZ'IsCommutative (negative (succ (succ b)) (succIsPositive (succ b))) (positive (succ (succ c)) (succIsPositive (succ c))) = diffProof' c b (succ (c +N succ b)) (c +N succ (succ b)) refl help (equalityCommutative (succExtracts c (succ b)))
          where
            help : (succ (c +N succ b)) ≡ c +N succ (succ b)
            help = _
        ans : negative 1 (succIsPositive zero) *Z' (positive (succ b) _ +Z' negative (succ c) _) ≡ positive 1 _ *Z' (negative (succ b) _ +Z' positive (succ c) _)
        ans = timesNegPosNeg zero b c
        ans' : negative 1 _ *Z' (positive (succ (succ b)) (succIsPositive (succ b)) +Z' negative (succ (succ c)) (succIsPositive (succ c))) ≡ negative 1 _ *Z' (positive (succ b) _ +Z' negative (succ c) _)
        ans' = applyEquality (λ t → negative 1 _ *Z' t) knocked
        ans'' : negative 1 _ *Z' (positive (succ (succ b)) (succIsPositive (succ b)) +Z' negative (succ (succ c)) (succIsPositive (succ c))) ≡ positive 1 _ *Z' (negative (succ b) _ +Z' positive (succ c) _)
        ans'' = identityOfIndiscernablesRight _ _ _ _≡_ ans' ans
    timesNegPosNeg (succ a) zero zero = refl
    timesNegPosNeg (succ a) zero (succ c) = refl
    timesNegPosNeg (succ a) (succ b) zero = refl
    timesNegPosNeg (succ a) (succ b) (succ c) = identityOfIndiscernablesRight _ _ _ _≡_ ans'' (applyEquality (λ t → positive (succ (succ a)) (succIsPositive (succ a)) *Z' t) (knocked'))
      where
        knocked : positive (succ (succ b)) (succIsPositive (succ b)) +Z' negative (succ (succ c)) (succIsPositive (succ c)) ≡ positive (succ b) _ +Z' negative (succ c) _
        knocked = canKnockOneOff+Z' (succ b) (succ c) {succIsPositive b} {succIsPositive c} {succIsPositive (succ b)} {succIsPositive (succ c)}
        knocked' : negative (succ b) (succIsPositive b) +Z' positive (succ c) (succIsPositive c) ≡ negative (succ (succ b)) (succIsPositive (succ b)) +Z' positive (succ (succ c)) (succIsPositive (succ c))
        knocked' rewrite additionZ'IsCommutative (negative (succ b) (succIsPositive b)) (positive (succ c) (succIsPositive c)) | additionZ'IsCommutative (negative (succ (succ b)) (succIsPositive (succ b))) (positive (succ (succ c)) (succIsPositive (succ c))) = diffProof' c b (succ (c +N succ b)) (c +N succ (succ b)) refl help (equalityCommutative (succExtracts c (succ b)))
          where
            help : (succ (c +N succ b)) ≡ c +N succ (succ b)
            help = _
        ans : negative (succ (succ a)) (succIsPositive (succ a)) *Z' (positive (succ b) _ +Z' negative (succ c) _) ≡ positive (succ (succ a)) (succIsPositive (succ a)) *Z' (negative (succ b) _ +Z' positive (succ c) _)
        ans = timesNegPosNeg (succ a) b c
        ans' : negative (succ (succ a)) (succIsPositive (succ a)) *Z' (positive (succ (succ b)) (succIsPositive (succ b)) +Z' negative (succ (succ c)) (succIsPositive (succ c))) ≡ negative (succ (succ a)) (succIsPositive (succ a)) *Z' (positive (succ b) _ +Z' negative (succ c) _)
        ans' = applyEquality (λ t → negative (succ (succ a)) (succIsPositive (succ a)) *Z' t) knocked
        ans'' : negative (succ (succ a)) (succIsPositive (succ a)) *Z' (positive (succ (succ b)) (succIsPositive (succ b)) +Z' negative (succ (succ c)) (succIsPositive (succ c))) ≡ positive (succ (succ a)) (succIsPositive (succ a)) *Z' (negative (succ b) _ +Z' positive (succ c) _)
        ans'' = identityOfIndiscernablesRight _ _ _ _≡_ ans' ans

    timesNegNegPos : (a b c : ℕ) → (negative (succ a) (succIsPositive a)) *Z' ((negative (succ b) (succIsPositive b)) +Z' (positive (succ c) (succIsPositive c))) ≡ (positive (succ a) (succIsPositive a)) *Z' ((positive (succ b) (succIsPositive b)) +Z' (negative (succ c) (succIsPositive c)))
    timesNegNegPos a b c rewrite additionZ'IsCommutative (negative (succ b) (succIsPositive b)) (positive (succ c) (succIsPositive c)) | additionZ'IsCommutative (positive (succ b) (succIsPositive b)) (negative (succ c) (succIsPositive c)) = timesNegPosNeg a c b

    additionZ'DistributiveMulZ' : (a b c : ℤSimple) → (a *Z' (b +Z' c)) ≡ (a *Z' b +Z' a *Z' c)
    additionZ'DistributiveMulZ' (negative zero (le x ())) b c
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative zero (le y ())) (negative c prC)
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative (succ b) prB) (negative zero (le y ()))
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative (succ b) prB) (negative (succ c) prC) = lemmaDistributive a (positive (succ b) prB) (positive (succ c) prC)
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative zero (le y ())) (positive c prC)
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative (succ b) prB) (positive zero (le y ()))
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative (succ b) prB) (positive (succ c) prC) rewrite <NRefl x (succIsPositive a) | <NRefl prB (succIsPositive b) | <NRefl prC (succIsPositive c) = help
      where
        inter : (negative (succ a) (succIsPositive a)) *Z' ((negative (succ b) (succIsPositive b)) +Z' (positive (succ c) (succIsPositive c))) ≡ positive (succ a) (succIsPositive a) *Z' (positive (succ b) (succIsPositive b) +Z' negative (succ c) (succIsPositive c))
        inter = timesNegNegPos a b c
        lhs : positive (succ a) (succIsPositive a) *Z' (positive (succ b) (succIsPositive b) +Z' negative (succ c) (succIsPositive c)) ≡ positive (succ a) (succIsPositive a) *Z' positive (succ b) (succIsPositive b) +Z' (negative (succ a) (succIsPositive a) *Z' positive (succ c) (succIsPositive c))
        lhs = lemmaDistributive a (positive (succ b) (succIsPositive b)) (negative (succ c) (succIsPositive c))
        help : (negative (succ a) (succIsPositive a)) *Z' ((negative (succ b) (succIsPositive b)) +Z' (positive (succ c) (succIsPositive c))) ≡ negative (succ a) (succIsPositive a) *Z' negative (succ b) (succIsPositive b) +Z' (negative (succ a) (succIsPositive a) *Z' positive (succ c) (succIsPositive c))
        help = transitivity inter lhs
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative zero (le y ())) zZero
    additionZ'DistributiveMulZ' (negative (succ a) x) (negative (succ b) prB) zZero = refl
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive b prB) (negative zero (le y ()))
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive zero (le y ())) (negative (succ c) prC)
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive (succ b) prB) (negative (succ c) prC) rewrite <NRefl x (succIsPositive a) | <NRefl prB (succIsPositive b) | <NRefl prC (succIsPositive c) = help
      where
        inter : (negative (succ a) (succIsPositive a)) *Z' ((positive (succ b) (succIsPositive b)) +Z' (negative (succ c) (succIsPositive c))) ≡ positive (succ a) (succIsPositive a) *Z' (negative (succ b) (succIsPositive b) +Z' positive (succ c) (succIsPositive c))
        inter = timesNegPosNeg a b c
        lhs : positive (succ a) (succIsPositive a) *Z' (negative (succ b) (succIsPositive b) +Z' positive (succ c) (succIsPositive c)) ≡ positive (succ a) (succIsPositive a) *Z' negative (succ b) (succIsPositive b) +Z' (positive (succ a) (succIsPositive a) *Z' positive (succ c) (succIsPositive c))
        lhs = lemmaDistributive a (negative (succ b) (succIsPositive b)) (positive (succ c) (succIsPositive c))
        help : (negative (succ a) (succIsPositive a)) *Z' ((positive (succ b) (succIsPositive b)) +Z' (negative (succ c) (succIsPositive c))) ≡ negative (succ a) (succIsPositive a) *Z' positive (succ b) (succIsPositive b) +Z' (negative (succ a) (succIsPositive a) *Z' negative (succ c) (succIsPositive c))
        help = transitivity inter lhs
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive b prB) (positive zero (le y ()))
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive 0 (le y ())) (positive (succ c) prC)
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive (succ b) prB) (positive (succ c) prC) rewrite timesNegPosPos a b c = applyEquality (λ t → negative (succ t) (succIsPositive t)) help
       where
         help : (b +N succ c) +N a *N succ (b +N succ c) ≡ (b +N a *N succ b) +N succ (c +N a *N succ c)
         help rewrite productDistributes a (succ b) (succ c) | equalityCommutative (additionNIsAssociative (b +N succ c) (a *N succ b) (a *N succ c)) | additionNIsAssociative b (succ c) (a *N succ b) | additionNIsCommutative (succ c) (a *N succ b) | equalityCommutative (additionNIsAssociative b (a *N succ b) (succ c)) | additionNIsAssociative (b +N a *N succ b) (succ c) (a *N succ c) = refl
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive zero (le y ())) zZero
    additionZ'DistributiveMulZ' (negative (succ a) x) (positive (succ b) prB) zZero = refl
    additionZ'DistributiveMulZ' (negative (succ a) x) zZero (negative zero (le y ()))
    additionZ'DistributiveMulZ' (negative (succ a) x) zZero (negative (succ c) prC) = refl
    additionZ'DistributiveMulZ' (negative (succ a) x) zZero (positive zero (le y ()))
    additionZ'DistributiveMulZ' (negative (succ a) x) zZero (positive (succ c) prC) = refl
    additionZ'DistributiveMulZ' (negative (succ a) x) zZero zZero = refl
    additionZ'DistributiveMulZ' (positive zero (le x ())) b c
    additionZ'DistributiveMulZ' (positive (succ a) x) b c rewrite <NRefl x (succIsPositive a) = lemmaDistributive a b c
    additionZ'DistributiveMulZ' zZero b c = refl

    additionZDistributiveMulZ : (a b c : ℤ) → (a *Z (b +Z c)) ≡ (a *Z b) +Z (a *Z c)
    additionZDistributiveMulZ a b c = identityOfIndiscernablesRight _ _ _ _≡_ lem12 (applyEquality (λ t → a *Z b +Z (a *Z t)) (zIsZ c))
      where
        lem1 : convertZ' ((convertZ a) *Z' ((convertZ b) +Z' (convertZ c))) ≡ convertZ' ((convertZ a *Z' convertZ b) +Z' (convertZ a *Z' convertZ c))
        lem2 : convertZ' (convertZ a) *Z convertZ' ((convertZ b) +Z' (convertZ c)) ≡ convertZ' ((convertZ a *Z' convertZ b) +Z' (convertZ a *Z' convertZ c))
        lem3 : a *Z convertZ' ((convertZ b) +Z' (convertZ c)) ≡ convertZ' ((convertZ a *Z' convertZ b) +Z' (convertZ a *Z' convertZ c))
        lem4 : a *Z (convertZ' (convertZ b) +Z convertZ' (convertZ c)) ≡ convertZ' ((convertZ a *Z' convertZ b) +Z' (convertZ a *Z' convertZ c))
        lem5 : a *Z (b +Z convertZ' (convertZ c)) ≡ convertZ' ((convertZ a *Z' convertZ b) +Z' (convertZ a *Z' convertZ c))
        lem6 : a *Z (b +Z c) ≡ convertZ' ((convertZ a *Z' convertZ b) +Z' (convertZ a *Z' convertZ c))
        lem7 : a *Z (b +Z c) ≡ convertZ' (convertZ a *Z' convertZ b) +Z convertZ' (convertZ a *Z' convertZ c)
        lem8 : a *Z (b +Z c) ≡ (convertZ' (convertZ a) *Z (convertZ' (convertZ b))) +Z convertZ' (convertZ a *Z' convertZ c)
        lem9 : a *Z (b +Z c) ≡ (a *Z (convertZ' (convertZ b))) +Z convertZ' (convertZ a *Z' convertZ c)
        lem10 : a *Z (b +Z c) ≡ (a *Z b) +Z convertZ' (convertZ a *Z' convertZ c)
        lem11 : a *Z (b +Z c) ≡ (a *Z b) +Z (convertZ' (convertZ a) *Z convertZ' (convertZ c))
        lem12 : a *Z (b +Z c) ≡ (a *Z b) +Z (a *Z convertZ' (convertZ c))
        lem12 = identityOfIndiscernablesRight _ _ _ _≡_ lem11 (applyEquality (λ t → a *Z b +Z (t *Z convertZ' (convertZ c))) (zIsZ a))
        lem11 = identityOfIndiscernablesRight _ _ _ _≡_ lem10 (applyEquality (λ t → a *Z b +Z t) (convertZ'DistributesOver*Z (convertZ a) _))
        lem10 = identityOfIndiscernablesRight _ _ _ _≡_ lem9 (applyEquality (λ t → a *Z t +Z convertZ' (convertZ a *Z' convertZ c)) (zIsZ b))
        lem9 = identityOfIndiscernablesRight _ _ _ _≡_ lem8 (applyEquality (λ t → t *Z (convertZ' (convertZ b)) +Z convertZ' (convertZ a *Z' convertZ c)) (zIsZ a))
        lem8 = identityOfIndiscernablesRight _ _ _ _≡_ lem7 (applyEquality (λ t → t +Z convertZ' (convertZ a *Z' convertZ c)) (convertZ'DistributesOver*Z (convertZ a) _))
        lem7 = identityOfIndiscernablesRight _ _ _ _≡_ lem6 (plusIsPlus (convertZ a *Z' convertZ b) _)
        lem6 = identityOfIndiscernablesLeft _ _ _ _≡_ lem5 (applyEquality (λ t → a *Z (b +Z t)) (zIsZ c))
        lem5 = identityOfIndiscernablesLeft _ _ _ _≡_ lem4 (applyEquality (λ t → a *Z (t +Z convertZ' (convertZ c))) (zIsZ b))
        lem4 = identityOfIndiscernablesLeft _ _ _ _≡_ lem3 (applyEquality (λ t → a *Z t) (plusIsPlus (convertZ b) _))
        lem3 = identityOfIndiscernablesLeft _ _ _ _≡_ lem2 (applyEquality (λ t → t *Z (convertZ' ((convertZ b) +Z' convertZ c))) (zIsZ a))
        lem2 = identityOfIndiscernablesLeft _ _ _ _≡_ lem1 (convertZ'DistributesOver*Z (convertZ a) _)
        lem1 = applyEquality convertZ' (additionZ'DistributiveMulZ' (convertZ a) (convertZ b) (convertZ c))

    additionZRespectsOrder : (a b c : ℤ) → (a <Z b) → (a +Z c <Z b +Z c)
    additionZRespectsOrder a b c (le x proof) = le x (identityOfIndiscernablesLeft ((nonneg (succ x) +Z a) +Z c) (b +Z c) (nonneg (succ x) +Z (a +Z c)) _≡_ (applyEquality (λ t → t +Z c) proof) (equalityCommutative (additionZIsAssociative (nonneg (succ x)) a c)))

    nonnegNotLessNegsucc : (a b : ℕ) → (nonneg a <Z negSucc b) → False
    nonnegNotLessNegsucc a b (le x proof) = nonnegIsNotNegsucc proof

    productOfPositivesIsPositive : (a b : ℤ) → (nonneg zero <Z a) → (nonneg zero <Z b) → (nonneg 0 <Z a *Z b)
    productOfPositivesIsPositive (nonneg zero) (nonneg b) pr1 pr2 = exFalso (lessZIrreflexive {nonneg 0} pr1)
    productOfPositivesIsPositive (nonneg (succ a)) (nonneg zero) pr1 pr2 = exFalso (lessZIrreflexive {nonneg 0} pr2)
    productOfPositivesIsPositive (nonneg (succ a)) (nonneg (succ b)) pr1 pr2 rewrite multiplyingNonnegIsHom (succ a) (succ b) = lessIsPreservedNToZ (succIsPositive (b +N a *N succ b))
    productOfPositivesIsPositive (nonneg zero) (negSucc b) pr1 pr2 = exFalso (nonnegNotLessNegsucc 0 b pr2)
    productOfPositivesIsPositive (nonneg (succ a)) (negSucc b) pr1 pr2 = exFalso (nonnegNotLessNegsucc 0 b pr2)
    productOfPositivesIsPositive (negSucc x) b pr1 pr2 = exFalso (nonnegNotLessNegsucc 0 x pr1)

    lessZTransitive : {a b c : ℤ} → (a <Z b) → (b <Z c) → (a <Z c)
    lessZTransitive {a} {b} {c} (le d1 pr1) (le d2 pr2) rewrite equalityCommutative pr1 = le (d1 +N succ d2) pr
      where
        pr : nonneg (succ (d1 +N succ d2)) +Z a ≡ c
        pr rewrite additionZIsAssociative (nonneg (succ d2)) (nonneg (succ d1)) a | additionNIsCommutative (succ d2) (succ d1) = pr2

    ℤGroup : Group (reflSetoid ℤ) (_+Z_)
    Group.wellDefined ℤGroup {a} {b} {.a} {.b} refl refl = refl
    Group.identity ℤGroup = nonneg zero
    Group.inverse ℤGroup = additiveInverseZ
    Group.multAssoc ℤGroup {a} {b} {c} = additionZIsAssociative a b c
    Group.multIdentLeft ℤGroup {a} = refl
    Group.multIdentRight ℤGroup {a} = zeroIsAdditiveIdentityRightZ a
    Group.invLeft ℤGroup {a} = addInverseLeftZ a
    Group.invRight ℤGroup {a} = addInverseRightZ a

    ℤAbGrp : AbelianGroup ℤGroup
    ℤAbGrp = record { commutative = λ {a} {b} → additionZIsCommutative a b }

    ℤRing : Ring (reflSetoid ℤ) (_+Z_) (_*Z_)
    Ring.additiveGroup ℤRing = ℤGroup
    Ring.multWellDefined ℤRing {r} {s} {.r} {.s} refl refl = refl
    Ring.1R ℤRing = nonneg (succ zero)
    Ring.groupIsAbelian ℤRing {a} {b} = additionZIsCommutative a b
    Ring.multAssoc ℤRing {a} {b} {c} = multiplicationZIsAssociative a b c
    Ring.multCommutative ℤRing {a} {b} = multiplicationZIsCommutative a b
    Ring.multDistributes ℤRing {a} {b} {c} = additionZDistributiveMulZ a b c
    Ring.multIdentIsIdent ℤRing {a} = multiplicativeIdentityOneZLeft a

    negsuccTimesNonneg : {a b : ℕ} → (negSucc a *Z nonneg (succ b)) ≡ nonneg 0 → False
    negsuccTimesNonneg {a} {b} pr with convertZ (negSucc a)
    negsuccTimesNonneg {a} {b} () | negative a₁ x
    negsuccTimesNonneg {a} {b} () | positive a₁ x
    negsuccTimesNonneg {a} {b} () | zZero

    negsuccTimesNegsucc : {a b : ℕ} → (negSucc a *Z negSucc b) ≡ nonneg 0 → False
    negsuccTimesNegsucc {a} {b} pr with convertZ (negSucc a)
    negsuccTimesNegsucc {a} {b} () | negative a₁ x
    negsuccTimesNegsucc {a} {b} () | positive a₁ x
    negsuccTimesNegsucc {a} {b} () | zZero

    ℤIntDom : IntegralDomain ℤRing
    IntegralDomain.intDom ℤIntDom {nonneg zero} {nonneg b} pr = inl refl
    IntegralDomain.intDom ℤIntDom {nonneg (succ a)} {nonneg zero} pr = inr refl
    IntegralDomain.intDom ℤIntDom {nonneg (succ a)} {nonneg (succ b)} pr = exFalso (naughtE (nonnegInjective (equalityCommutative (transitivity (equalityCommutative (multiplyingNonnegIsHom (succ a) (succ b))) pr))))
    IntegralDomain.intDom ℤIntDom {nonneg zero} {negSucc b} pr = inl refl
    IntegralDomain.intDom ℤIntDom {nonneg (succ a)} {negSucc b} pr = exFalso (negsuccTimesNonneg {b} {a} (transitivity (multiplicationZIsCommutative (negSucc b) (nonneg (succ a))) pr))
    IntegralDomain.intDom ℤIntDom {negSucc a} {nonneg zero} pr = inr refl
    IntegralDomain.intDom ℤIntDom {negSucc a} {nonneg (succ b)} pr = exFalso (negsuccTimesNonneg {a} {b} pr)
    IntegralDomain.intDom ℤIntDom {negSucc a} {negSucc b} pr = exFalso (negsuccTimesNegsucc {a} {b} pr)
    IntegralDomain.nontrivial ℤIntDom = λ ()

    ℤOrder : TotalOrder ℤ
    PartialOrder._<_ (TotalOrder.order ℤOrder) = _<Z_
    TotalOrder.totality ℤOrder a b = lessThanTotalZ {a} {b}
    PartialOrder.irreflexive (TotalOrder.order ℤOrder) = lessZIrreflexive
    PartialOrder.transitive (TotalOrder.order ℤOrder) {a} {b} {c} = lessZTransitive

    ℤOrderedRing : OrderedRing ℤRing (totalOrderToSetoidTotalOrder ℤOrder)
    OrderedRing.orderRespectsAddition ℤOrderedRing {a} {b} a<b c = additionZRespectsOrder a b c a<b
    OrderedRing.orderRespectsMultiplication ℤOrderedRing {a} {b} a<b = productOfPositivesIsPositive a b a<b

    _-Z_ : ℤ → ℤ → ℤ
    a -Z b = a +Z (additiveInverseZ b)
