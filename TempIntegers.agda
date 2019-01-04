{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Naturals
open import Groups
open import Rings
open import Integers

module TempIntegers where

    additiveInverseExists : (a : ℕ) → (negSucc a +Z nonneg (succ a)) ≡ nonneg 0
    additiveInverseExists zero = refl
    additiveInverseExists (succ a) = additiveInverseExists a

    multiplicationZIsCommutativeNonnegNegsucc : (a b : ℕ) → (nonneg a *Z negSucc b) ≡ negSucc b *Z nonneg a
    multiplicationZIsCommutativeNonnegNegsucc zero zero = refl
    multiplicationZIsCommutativeNonnegNegsucc zero (succ b) = refl
    multiplicationZIsCommutativeNonnegNegsucc (succ a) zero = refl
    multiplicationZIsCommutativeNonnegNegsucc (succ x) (succ y) = t
      where
        r : (nonneg (succ x) *Z negSucc y) ≡ (negSucc y) *Z (nonneg (succ x))
        r = multiplicationZIsCommutativeNonnegNegsucc (succ x) y
        s : negSucc x +Z (nonneg (succ x) *Z negSucc y) ≡ negSucc x +Z negSucc y *Z (nonneg (succ x))
        s = applyEquality (_+Z_ (negSucc x)) r
        t : negSucc x +Z (nonneg (succ x) *Z negSucc y) ≡ negSucc y *Z (nonneg (succ x)) +Z negSucc x
        t = identityOfIndiscernablesRight (negSucc x +Z (nonneg (succ x) *Z negSucc y)) (negSucc x +Z negSucc y *Z (nonneg (succ x))) (negSucc y *Z nonneg (succ x) +Z negSucc x) _≡_ s (additionZIsCommutative (negSucc x) (negSucc y *Z nonneg (succ x)))

    multiplicationZIsCommutative : (a b : ℤ) → (a *Z b) ≡ (b *Z a)
    multiplicationZIsCommutative (nonneg x) (nonneg y) = applyEquality nonneg (multiplicationNIsCommutative x y)
    multiplicationZIsCommutative (nonneg x) (negSucc y) = multiplicationZIsCommutativeNonnegNegsucc x y
    multiplicationZIsCommutative (negSucc x) (nonneg y) = equalityCommutative (multiplicationZIsCommutativeNonnegNegsucc y x)
    multiplicationZIsCommutative (negSucc zero) (negSucc y) = applyEquality nonneg (applyEquality succ n)
      where
        k : succ zero *N succ y ≡ succ y *N succ zero
        k = multiplicationNIsCommutative (succ zero) (succ y)
        j : succ y +N zero *N succ y ≡ succ zero +N y *N succ zero
        j = transitivity refl (transitivity k refl)
        alterL : y +N succ (zero *N succ y) ≡ succ zero +N y *N succ zero
        alterL = identityOfIndiscernablesLeft (succ y +N zero *N succ y) (succ zero +N y *N succ zero) (y +N succ (zero *N succ y)) _≡_ j (equalityCommutative (succCanMove y (zero *N succ y)))
        j' : y +N succ (zero *N succ y) ≡ zero +N succ (y *N succ zero)
        j' = identityOfIndiscernablesRight (y +N succ (zero *N succ y)) (succ zero +N y *N succ zero) (zero +N succ (y *N succ zero)) _≡_ alterL (equalityCommutative (succCanMove zero (y *N succ zero)))
        m : succ (y +N zero *N succ y) ≡ zero +N succ (y *N succ zero)
        m = identityOfIndiscernablesLeft (y +N succ (zero *N succ y)) (zero +N succ (y *N succ zero)) (succ (y +N zero *N succ y)) _≡_ j' (succExtracts y (zero *N succ y))
        m' : succ (y +N zero *N succ y) ≡ succ (zero +N y *N succ zero)
        m' = identityOfIndiscernablesRight (succ (y +N zero *N succ y)) (zero +N succ (y *N succ zero)) (succ (zero +N y *N succ zero)) _≡_ m (succExtracts zero (y *N succ zero))
        n : y +N zero *N succ y ≡ zero +N y *N succ zero
        n = succInjective m'
    multiplicationZIsCommutative (negSucc (succ x)) (negSucc y) = applyEquality nonneg (applyEquality succ n)
      where
        k : succ (succ x) *N succ y ≡ succ y *N succ (succ x)
        k = multiplicationNIsCommutative (succ (succ x)) (succ y)
        j : succ y +N (succ x) *N succ y ≡ succ (succ x) +N y *N succ (succ x)
        j = transitivity refl (transitivity k refl)
        alterL : y +N succ ((succ x) *N succ y) ≡ succ (succ x) +N y *N succ (succ x)
        alterL = identityOfIndiscernablesLeft (succ y +N (succ x) *N succ y) (succ (succ x) +N y *N succ (succ x)) (y +N succ ((succ x) *N succ y)) _≡_ j (equalityCommutative (succCanMove y ((succ x) *N succ y)))
        j' : y +N succ ((succ x) *N succ y) ≡ (succ x) +N succ (y *N succ (succ x))
        j' = identityOfIndiscernablesRight (y +N succ ((succ x) *N succ y)) (succ (succ x) +N y *N succ (succ x)) ((succ x) +N succ (y *N succ (succ x))) _≡_ alterL (equalityCommutative (succCanMove (succ x) (y *N succ (succ x))))
        m : succ (y +N (succ x) *N succ y) ≡ (succ x) +N succ (y *N succ (succ x))
        m = identityOfIndiscernablesLeft (y +N succ ((succ x) *N succ y)) ((succ x) +N succ (y *N succ (succ x))) (succ (y +N (succ x) *N succ y)) _≡_ j' (succExtracts y ((succ x) *N succ y))
        m' : succ (y +N (succ x) *N succ y) ≡ succ ((succ x) +N y *N succ (succ x))
        m' = identityOfIndiscernablesRight (succ (y +N (succ x) *N succ y)) ((succ x) +N succ (y *N succ (succ x))) (succ ((succ x) +N y *N succ (succ x))) _≡_ m (succExtracts (succ x) (y *N succ (succ x)))
        n : y +N (succ x) *N succ y ≡ (succ x) +N y *N succ (succ x)
        n = succInjective m'

    negSuccIsNotNonneg : (a b : ℕ) → (negSucc a ≡ nonneg b) → False
    negSuccIsNotNonneg zero b ()
    negSuccIsNotNonneg (succ a) b ()

    negSuccInjective : {a b : ℕ} → (negSucc a ≡ negSucc b) → a ≡ b
    negSuccInjective refl = refl

    zeroMultInZLeft : (a : ℤ) → (nonneg zero) *Z a ≡ (nonneg zero)
    zeroMultInZLeft a = identityOfIndiscernablesLeft (a *Z nonneg zero) (nonneg zero) (nonneg zero *Z a) _≡_ (zeroMultInZRight a) (multiplicationZIsCommutative a (nonneg zero))

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
    multiplicativeIdentityOneZNegsucc (succ x) = i
      where
        inter : negSucc x *Z nonneg (succ zero) ≡ negSucc x
        i : negSucc x *Z nonneg (succ zero) +Z negSucc zero ≡ negSucc (succ x)
        inter = multiplicativeIdentityOneZNegsucc x
        h = applyEquality (λ x → x +Z negSucc zero) inter
        i = identityOfIndiscernablesRight (negSucc x *Z nonneg (succ zero) +Z negSucc zero) (negSucc x +Z negSucc zero) (negSucc (succ x)) _≡_ h (canAddOneReversed (negSucc x) x refl)

    multiplicativeIdentityOneZ : (a : ℤ) → (a *Z nonneg (succ zero) ≡ a)
    multiplicativeIdentityOneZ (nonneg x) = applyEquality nonneg (productWithOneRight x)
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

    lessNegsuccNonneg : {a b : ℕ} → (negSucc a <Z nonneg b)
    lessNegsuccNonneg {a} {b} = record { x = x ; proof = pr }
      where
        x : ℕ
        x = a +N b
        pr' : nonneg (succ (a +N b)) ≡ nonneg b +Z nonneg (succ a)
        pr' rewrite addingNonnegIsHom b (succ a) | additionNIsCommutative b (succ a) = refl
        pr : nonneg (succ x) +Z negSucc a ≡ nonneg b
        pr rewrite additionZIsCommutative (nonneg (succ x)) (negSucc a) = moveNegsuccConverse a (nonneg (succ (a +N b))) (nonneg b) pr'


    moveNegsuccTimes : (a b : ℤ) (c : ℕ) → (a *Z (negSucc c)) ≡ b → b +Z (a *Z nonneg (succ c)) ≡ nonneg 0
    moveNegsuccTimes (nonneg zero) (nonneg b) c pr rewrite multiplyWithZero' (negSucc c) | additionZIsCommutative (nonneg b) (nonneg 0) = equalityCommutative pr
    moveNegsuccTimes (nonneg (succ a)) (nonneg b) zero ()
    moveNegsuccTimes (nonneg (succ a)) (nonneg b) (succ c) pr = {!!}
    moveNegsuccTimes (negSucc a) (nonneg b) c pr = {!!}
    moveNegsuccTimes (nonneg 0) (negSucc b) c pr = {!!}
    moveNegsuccTimes (nonneg (succ a)) (negSucc b) c pr = {!!}
    moveNegsuccTimes (negSucc a) (negSucc b) c pr = {!!}

    multiplicationZIsAssociative : (a b c : ℤ) → (a *Z (b *Z c)) ≡ (a *Z b) *Z c
    multiplicationZIsAssociative (nonneg x) (nonneg x₁) (nonneg x₂) = applyEquality nonneg (multiplicationNIsAssociative x x₁ x₂)
    multiplicationZIsAssociative (nonneg x) (nonneg zero) (negSucc zero) = p
      where
        a : x *N zero ≡ zero
        a = productZeroIsZeroRight x
        q : nonneg zero ≡ nonneg zero *Z negSucc zero
        q = refl
        r : nonneg (x *N zero) ≡ nonneg zero *Z negSucc zero
        r = identityOfIndiscernablesLeft (nonneg zero) (nonneg zero *Z negSucc zero) (nonneg (x *N zero)) _≡_ q (applyEquality nonneg (equalityCommutative a))
        r' : nonneg zero *Z negSucc zero ≡ nonneg (x *N zero) *Z negSucc zero
        r' = applyEquality (λ n → n *Z negSucc zero) (applyEquality nonneg (equalityCommutative a))
        p : nonneg (x *N zero) ≡ nonneg (x *N zero) *Z negSucc zero
        p = identityOfIndiscernablesRight (nonneg (x *N zero)) (nonneg zero *Z negSucc zero) (nonneg (x *N zero) *Z negSucc zero) _≡_ r r'
    multiplicationZIsAssociative (nonneg zero) (nonneg (succ y)) (negSucc zero) = zeroMultInZLeft (negSucc y)
    multiplicationZIsAssociative (nonneg zero) (nonneg (succ y)) (negSucc (succ z)) = zeroMultInZLeft (negSucc y +Z nonneg (succ y) *Z negSucc z)
    multiplicationZIsAssociative (nonneg (succ x)) (nonneg (succ y)) (negSucc zero) = {!!}
    -- moveNegsucc : (a : ℕ) (b c : ℤ) → (negSucc a) +Z b ≡ c → b ≡ c +Z (nonneg (succ a))
    multiplicationZIsAssociative (nonneg (succ x)) (nonneg (succ y)) (negSucc (succ z)) = {!!}
    multiplicationZIsAssociative (nonneg x) (negSucc b) (nonneg c) = {!!}
    multiplicationZIsAssociative (nonneg x) (negSucc b) (negSucc c) = {!!}
    multiplicationZIsAssociative (negSucc x) (nonneg b) (nonneg c) = {!!}
    multiplicationZIsAssociative (negSucc x) (nonneg b) (negSucc c) = {!!}
    multiplicationZIsAssociative (negSucc x) (negSucc b) (nonneg c) = {!!}
    multiplicationZIsAssociative (negSucc x) (negSucc b) (negSucc c) = {!!}
    multiplicationZIsAssociative (nonneg x) (nonneg zero) (negSucc (succ z)) = {!!}

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

    addZDistributiveMulZ : (a b c : ℤ) → (a *Z (b +Z c)) ≡ (a *Z b +Z a *Z c)
    addZDistributiveMulZ (nonneg a) (nonneg b) (nonneg c) rewrite addingNonnegIsHom b c | multiplyingNonnegIsHom a (b +N c) | addingNonnegIsHom (a *N b) (a *N c) = applyEquality nonneg (productDistributes a b c)
    addZDistributiveMulZ (nonneg zero) (nonneg zero) (negSucc zero) = refl
    addZDistributiveMulZ (nonneg zero) (nonneg zero) (negSucc (succ c)) = refl
    addZDistributiveMulZ (nonneg zero) (nonneg (succ b)) (negSucc zero) = refl
    addZDistributiveMulZ (nonneg zero) (nonneg (succ b)) (negSucc (succ c)) rewrite multiplicationZIsCommutative (nonneg zero) (nonneg b +Z negSucc c) = multiplyWithZero (nonneg b +Z negSucc c)
    addZDistributiveMulZ (nonneg (succ a)) (nonneg zero) (negSucc zero) rewrite multiplicationNIsCommutative a zero = refl
    addZDistributiveMulZ (nonneg (succ a)) (nonneg zero) (negSucc (succ c)) rewrite multiplicationNIsCommutative a zero = refl
    addZDistributiveMulZ (nonneg (succ a)) (nonneg (succ b)) (negSucc zero) = identityOfIndiscernablesRight (nonneg (b +N (a *N b))) (negSucc a +Z nonneg (succ (b +N a *N succ b))) (nonneg (succ (b +N a *N succ b)) +Z negSucc a) _≡_ p (additionZIsCommutative (negSucc a) (nonneg (succ (b +N a *N succ b))))
      where
        p : nonneg (b +N (a *N b)) ≡ (negSucc a) +Z (nonneg (succ (b +N a *N succ b)))
        q : nonneg (succ (b +N a *N succ b)) ≡ nonneg (b +N a *N b) +Z nonneg (succ a)
        r : succ a *N succ b ≡ succ a +N (succ a *N b)
        r' : succ a *N succ b ≡ succ a +N (b *N succ a)
        r' rewrite multiplicationNIsCommutative (succ a) (succ b) = refl
        r rewrite multiplicationNIsCommutative (succ a) b = r'
        p = equalityCommutative (moveNegsuccConverse a (nonneg (succ (b +N a *N succ b))) (nonneg (b +N a *N b)) q)
        q rewrite addingNonnegIsHom (b +N a *N b) (succ a) | additionNIsCommutative (b +N a *N b) (succ a) = applyEquality (λ t → nonneg t) r
    addZDistributiveMulZ (nonneg (succ a)) (nonneg (succ b)) (negSucc (succ c)) = {!!}
    addZDistributiveMulZ (nonneg zero) (negSucc b) (nonneg c) rewrite additionZIsCommutative (nonneg zero *Z negSucc b) (nonneg zero) | multiplyWithZero' (negSucc b) | multiplyWithZero' (negSucc b +Z nonneg c) = refl
    addZDistributiveMulZ (nonneg (succ a)) (negSucc b) (nonneg c) = {!!}
    addZDistributiveMulZ (nonneg zero) (negSucc b) (negSucc c) rewrite multiplyWithZero' (negSucc b +Z negSucc c) | multiplyWithZero' (negSucc b) | multiplyWithZero' (negSucc c) = refl
    addZDistributiveMulZ (nonneg (succ a)) (negSucc zero) (negSucc c) = refl
    addZDistributiveMulZ (nonneg (succ a)) (negSucc (succ b)) (negSucc zero) rewrite additionNIsCommutative b 1 | additionZIsCommutative (negSucc a +Z nonneg (succ a) *Z negSucc b) (negSucc a) = refl
    addZDistributiveMulZ (nonneg (succ a)) (negSucc (succ b)) (negSucc (succ c)) = {!!}
    addZDistributiveMulZ (negSucc a) b c = {!!}

    zGroup : group {_} {ℤ}
    group._·_ zGroup = _+Z_
    group.identity zGroup = nonneg zero
    group.inv zGroup = additiveInverseZ
    group.multAssoc zGroup {a} {b} {c} = additionZIsAssociative a b c
    group.multIdentLeft zGroup {a} = refl
    group.multIdentRight zGroup {a} = zeroIsAdditiveIdentityRightZ a
    group.invLeft zGroup {a} = addInverseLeftZ a
    group.invRight zGroup {a} = addInverseRightZ a

    zRing : ring {_} {ℤ}
    ring.additiveGroup zRing = zGroup
    ring._*_ zRing = _*Z_
    ring.multIdent zRing = nonneg (succ zero)
    ring.groupIsAbelian zRing {a} {b} = additionZIsCommutative a b
    ring.multAssoc zRing {a} {b} {c} = multiplicationZIsAssociative a b c
    ring.multCommutative zRing {a} {b} = multiplicationZIsCommutative a b
    ring.multDistributes zRing {a} {b} {c} = addZDistributiveMulZ a b c
    ring.multIdentIsIdent zRing {a} = multiplicativeIdentityOneZLeft a

    -- TODO: ordered ring axioms
