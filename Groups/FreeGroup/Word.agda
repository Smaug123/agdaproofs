{-# OPTIONS --safe --warning=error #-}

open import Setoids.Setoids
open import Groups.SymmetricGroups.Definition
open import Groups.FreeGroup.Definition
open import Decidable.Sets
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import LogicalFormulae

module Groups.FreeGroup.Word {a : _} {A : Set a} (decA : DecidableSet A) where

data ReducedWord : Set a
wordLength : ReducedWord → ℕ
firstLetter : (w : ReducedWord) → .(0 <N wordLength w) → FreeCompletion A

data PrependIsValid (w : ReducedWord) (l : FreeCompletion A) : Set a where
  wordEmpty : wordLength w ≡ 0 → PrependIsValid w l
  wordEnding : .(pr : 0 <N wordLength w) → .(freeCompletionEqual decA l (freeInverse (firstLetter w pr)) ≡ BoolFalse) → PrependIsValid w l

data ReducedWord where
  empty : ReducedWord
  prependLetter : (letter : FreeCompletion A) → (w : ReducedWord) → PrependIsValid w letter → ReducedWord

firstLetter empty ()
firstLetter (prependLetter letter w x) pr = letter

wordLength empty = 0
wordLength (prependLetter letter w pr) = succ (wordLength w)

prependLetterRefl : {x : FreeCompletion A} {w : ReducedWord} → {pr1 pr2 : PrependIsValid w x} → prependLetter x w pr1 ≡ prependLetter x w pr2
prependLetterRefl {x} {empty} {wordEmpty refl} {wordEmpty refl} = refl
prependLetterRefl {x} {empty} {wordEmpty refl} {wordEnding () x₂}
prependLetterRefl {x} {empty} {wordEnding () x₁} {pr2}
prependLetterRefl {x} {prependLetter letter w x₁} {wordEmpty ()} {pr2}
prependLetterRefl {x} {prependLetter letter w x₁} {wordEnding pr x₂} {wordEmpty ()}
prependLetterRefl {x} {prependLetter letter w x₁} {wordEnding pr2 r2} {wordEnding pr1 r1} = refl

prependLetterInjective : {x : FreeCompletion A} {w1 w2 : ReducedWord} {pr1 : PrependIsValid w1 x} {pr2 : PrependIsValid w2 x} → prependLetter x w1 pr1 ≡ prependLetter x w2 pr2 → w1 ≡ w2
prependLetterInjective {x = x} {empty} {empty} {pr1} {pr2} pr = refl
prependLetterInjective {x = x} {prependLetter l1 w1 x1} {prependLetter .l1 .w1 .x1} {wordEnding pr₁ x₁} {wordEnding pr₂ x₂} refl = refl

prependLetterInjective' : {x y : FreeCompletion A} {w1 w2 : ReducedWord} {pr1 : PrependIsValid w1 x} {pr2 : PrependIsValid w2 y} → prependLetter x w1 pr1 ≡ prependLetter y w2 pr2 → x ≡ y
prependLetterInjective' refl = refl

badPrepend : {x : A} {w : ReducedWord} {pr : PrependIsValid w (ofInv x)} → (PrependIsValid (prependLetter (ofInv x) w pr) (ofLetter x)) → False
badPrepend (wordEmpty ())
badPrepend {x = x} (wordEnding pr bad) with DecidableSet.eq (decidableFreeCompletion decA) (ofLetter x) (ofLetter x)
badPrepend {x} (wordEnding pr ()) | inl x₁
badPrepend {x} (wordEnding pr bad) | inr pr2 = pr2 refl

badPrepend' : {x : A} {w : ReducedWord} {pr : PrependIsValid w (ofLetter x)} → (PrependIsValid (prependLetter (ofLetter x) w pr) (ofInv x)) → False
badPrepend' (wordEmpty ())
badPrepend' {x = x} (wordEnding pr x₁) with DecidableSet.eq (decidableFreeCompletion decA) (ofInv x) (ofInv x)
badPrepend' {x} (wordEnding pr ()) | inl x₂
badPrepend' {x} (wordEnding pr x₁) | inr pr2 = pr2 refl

data FreeGroupGenerators : Set a where
  χ : A → FreeGroupGenerators

freeGroupGenerators : (w : FreeGroupGenerators) → SymmetryGroupElements (reflSetoid (ReducedWord))
freeGroupGenerators (χ x) = sym {f = f} bij
  where
    open DecidableSet decA
    f : ReducedWord → ReducedWord
    f empty = prependLetter (ofLetter x) empty (wordEmpty refl)
    f (prependLetter (ofLetter startLetter) w pr) = prependLetter (ofLetter x) (prependLetter (ofLetter startLetter) w pr) (wordEnding (succIsPositive _) ans)
      where
        ans : freeCompletionEqual decA (ofLetter x) (ofInv startLetter) ≡ BoolFalse
        ans with DecidableSet.eq (decidableFreeCompletion decA) (ofLetter x) (ofInv startLetter)
        ... | bl = refl
    f (prependLetter (ofInv startLetter) w pr) with DecidableSet.eq decA startLetter x
    f (prependLetter (ofInv startLetter) w pr) | inl startLetter=x = w
    f (prependLetter (ofInv startLetter) w pr) | inr startLetter!=x = prependLetter (ofLetter x) (prependLetter (ofInv startLetter) w pr) (wordEnding (succIsPositive _) ans)
      where
        ans : freeCompletionEqual decA (ofLetter x) (ofLetter startLetter) ≡ BoolFalse
        ans with DecidableSet.eq (decidableFreeCompletion decA) (ofLetter x) (ofInv startLetter)
        ans | bl with DecidableSet.eq decA x startLetter
        ans | bl | inl x=sl = exFalso (startLetter!=x (equalityCommutative x=sl))
        ans | bl | inr x!=sl = refl
    bij : SetoidBijection (reflSetoid ReducedWord) (reflSetoid ReducedWord) f
    SetoidInjection.wellDefined (SetoidBijection.inj bij) x=y rewrite x=y = refl
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {empty} fx=fy = refl
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofLetter x₁) y pr1} ()
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) y pr1} fx=fy with DecidableSet.eq decA l x
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) empty (wordEmpty x₁)} () | inl l=x
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) empty (wordEnding () x₁)} fx=fy | inl l=x
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) (prependLetter (ofLetter x₂) y x₁) (wordEmpty ())} fx=fy | inl l=x
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) (prependLetter (ofLetter x₂) y x₁) (wordEnding pr bad)} fx=fy | inl refl with ofLetterInjective (prependLetterInjective' fx=fy)
    ... | l=x2 = exFalso ((freeCompletionEqualFalse' decA bad) (applyEquality ofInv l=x2))
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) (prependLetter (ofInv x₂) y x₁) pr1} () | inl l=x
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) y pr1} fx=fy | inr l!=x with prependLetterInjective fx=fy
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) y pr1} fx=fy | inr l!=x | ()
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter x) w1 prX} {empty} fx=fy with prependLetterInjective fx=fy
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter x) w1 prX} {empty} fx=fy | ()
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter x) w1 prX} {prependLetter (ofLetter y) w2 prY} fx=fy = prependLetterInjective fx=fy
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) w2 prY} fx=fy with DecidableSet.eq decA y x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) empty prY} () | inl y=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) (prependLetter (ofLetter b) w2 x₁) prY} fx=fy | inl y=x with ofLetterInjective (prependLetterInjective' fx=fy)
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) (prependLetter (ofLetter b) w2 x₁) (wordEmpty ())} fx=fy | inl y=x | x=b
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) (prependLetter (ofLetter b) w2 x₁) (wordEnding pr bad)} fx=fy | inl y=x | x=b rewrite x=b | y=x = exFalso (freeCompletionEqualFalse' decA bad refl)
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) (prependLetter (ofInv b) w2 x₁) prY} fx=fy | inl y=x with prependLetterInjective' fx=fy
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) (prependLetter (ofInv b) w2 x₁) prY} fx=fy | inl y=x | ()
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofLetter a) w1 prX} {prependLetter (ofInv y) w2 prY} fx=fy | inr y!=x with prependLetterInjective fx=fy
    ... | bl = bl
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {empty} fx=fy with DecidableSet.eq decA a x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) empty prX} {empty} () | inl a=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofLetter x₂) w1 x₁) prX} {empty} fx=fy | inl a=x with ofLetterInjective (prependLetterInjective' fx=fy)
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofLetter x₂) w1 x₁) (wordEmpty ())} {empty} fx=fy | inl a=x | x2=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofLetter x₂) w1 x₁) (wordEnding pr x3)} {empty} fx=fy | inl a=x | x2=x with freeCompletionEqualFalse' decA x3
    ... | bl = exFalso (bl (applyEquality ofInv (transitivity a=x (equalityCommutative x2=x))))
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofInv x₂) w1 x₁) prX} {empty} () | inl a=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {empty} () | inr a!=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofLetter x₁) y x₂} fx=fy with DecidableSet.eq decA a x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) empty prX} {prependLetter (ofLetter b) y x₂} () | inl a=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofLetter x₃) w1 x₁) prX} {prependLetter (ofLetter b) y x₂} fx=fy | inl a=x with ofLetterInjective (prependLetterInjective' fx=fy)
    ... | x3=x rewrite a=x | x3=x = exFalso (badPrepend' prX)
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofInv x₃) w1 x₁) prX} {prependLetter (ofLetter b) y x₂} fx=fy | inl a=x with prependLetterInjective' fx=fy
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofInv x₃) w1 x₁) prX} {prependLetter (ofLetter b) y x₂} fx=fy | inl a=x | ()
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofLetter x₁) y x₂} () | inr a!=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv x₁) y x₂} fx=fy with DecidableSet.eq decA a x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv b) y x₂} fx=fy | inl a=x with DecidableSet.eq decA b x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv b) y x₂} fx=fy | inl a=x | inl b=x rewrite fx=fy | a=x | b=x = prependLetterRefl
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) empty prX} {prependLetter (ofInv b) y x₂} () | inl a=x | inr b!=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofLetter x₃) w1 x₁) prX} {prependLetter (ofInv b) y x₂} fx=fy | inl a=x | inr b!=x with ofLetterInjective (prependLetterInjective' fx=fy)
    ... | x3=x rewrite a=x | x3=x = exFalso (badPrepend' prX)
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) (prependLetter (ofInv x₃) w1 x₁) prX} {prependLetter (ofInv b) y x₂} () | inl a=x | inr b!=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv b) y x₂} fx=fy | inr a!=x with DecidableSet.eq decA b x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv b) empty x₂} () | inr a!=x | inl b=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv b) (prependLetter (ofLetter x₃) y x₁) x2} fx=fy | inr a!=x | inl b=x with ofLetterInjective (prependLetterInjective' fx=fy)
    ... | x3=x rewrite (equalityCommutative x3=x) | b=x = exFalso (badPrepend' x2)
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv b) (prependLetter (ofInv x₃) y x₁) x₂} () | inr a!=x | inl b=x
    SetoidInjection.injective (SetoidBijection.inj bij) {prependLetter (ofInv a) w1 prX} {prependLetter (ofInv b) y x₂} fx=fy | inr a!=x | inr b!=x = prependLetterInjective fx=fy
    SetoidSurjection.wellDefined (SetoidBijection.surj bij) x=y rewrite x=y = refl
    SetoidSurjection.surjective (SetoidBijection.surj bij) {empty} = prependLetter (ofInv x) empty (wordEmpty refl) , needed
      where
        needed : f (prependLetter (ofInv x) empty (wordEmpty refl)) ≡ empty
        needed with DecidableSet.eq decA x x
        needed | inl x₁ = refl
        needed | inr x!=x = exFalso (x!=x refl)
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter l) empty pr} with DecidableSet.eq decA x l
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter x) empty (wordEmpty refl)} | inl refl = empty , refl
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter x) empty (wordEnding () x₁)} | inl refl
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter l) empty pr} | inr x!=l = prependLetter (ofInv x) (prependLetter (ofLetter l) empty pr) (wordEnding (succIsPositive _) (freeCompletionEqualFalse decA (λ p → x!=l (ofInvInjective p)))) , needed
      where
        needed : f (prependLetter (ofInv x) (prependLetter (ofLetter l) empty pr) (wordEnding (succIsPositive 0) (freeCompletionEqualFalse decA {ofInv x} {ofInv l} λ p → x!=l (ofInvInjective p)))) ≡ prependLetter (ofLetter l) empty pr
        needed with DecidableSet.eq decA x x
        ... | inl _ = refl
        ... | inr bad = exFalso (bad refl)
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter l) (prependLetter letter w pr2) pr} with DecidableSet.eq decA l x
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter l) (prependLetter (ofLetter y) w pr2) pr} | inl l=x rewrite l=x = prependLetter (ofLetter y) w pr2 , prependLetterRefl
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter l) (prependLetter (ofInv y) w pr2) pr} | inl l=x = prependLetter (ofInv y) w pr2 , needed
      where
        needed : f (prependLetter (ofInv y) w pr2) ≡ prependLetter (ofLetter l) (prependLetter (ofInv y) w pr2) pr
        needed with DecidableSet.eq decA y x
        needed | inl y=x rewrite l=x | y=x = exFalso (badPrepend pr)
        needed | inr y!=x rewrite l=x = prependLetterRefl
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter l) (prependLetter letter w pr2) pr} | inr l!=x = prependLetter (ofInv x) (prependLetter (ofLetter l) (prependLetter letter w pr2) pr) (wordEnding (succIsPositive _) (freeCompletionEqualFalse decA λ p → l!=x (ofInvInjective (equalityCommutative p)))) , needed
      where
        needed : f (prependLetter (ofInv x) (prependLetter (ofLetter l) (prependLetter letter w pr2) pr) (wordEnding (succIsPositive (succ (wordLength w))) (freeCompletionEqualFalse decA (λ p → l!=x (ofInvInjective (equalityCommutative p)))))) ≡ prependLetter (ofLetter l) (prependLetter letter w pr2) pr
        needed with DecidableSet.eq decA x x
        needed | inl x₁ = refl
        needed | inr x!=x = exFalso (x!=x refl)
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofInv l) w pr} = prependLetter (ofInv x) (prependLetter (ofInv l) w pr) (wordEnding (succIsPositive _) (freeCompletionEqualFalse decA {ofInv x} {ofLetter l} λ ())) , needed
      where
        needed : f (prependLetter (ofInv x) (prependLetter (ofInv l) w pr) (wordEnding (succIsPositive (wordLength w)) (freeCompletionEqualFalse decA {ofInv x} {ofLetter l} λ ()))) ≡ (prependLetter (ofInv l) w pr)
        needed with DecidableSet.eq decA x x
        needed | inl x₁ = refl
        needed | inr x!=x = exFalso (x!=x refl)
