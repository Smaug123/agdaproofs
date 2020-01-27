{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import WithK
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.WithK
open import Sets.FinSet.Definition
open import Groups.Definition
open import Groups.SymmetricGroups.Definition
open import Decidable.Sets

module Groups.FreeGroups where

data FreeCompletion {a : _} (A : Set a) : Set a where
  ofLetter : A → FreeCompletion A
  ofInv : A → FreeCompletion A

freeInverse : {a : _} {A : Set a} (l : FreeCompletion A) → FreeCompletion A
freeInverse (ofLetter x) = ofInv x
freeInverse (ofInv x) = ofLetter x

ofLetterInjective : {a : _} {A : Set a} {x y : A} → (ofLetter x ≡ ofLetter y) → x ≡ y
ofLetterInjective refl = refl

ofInvInjective : {a : _} {A : Set a} {x y : A} → (ofInv x ≡ ofInv y) → x ≡ y
ofInvInjective refl = refl

decidableFreeCompletion : {a : _} {A : Set a} → DecidableSet A → DecidableSet (FreeCompletion A)
decidableFreeCompletion {A = A} record { eq = dec } = record { eq = pr }
  where
    pr : (a b : FreeCompletion A) → (a ≡ b) || (a ≡ b → False)
    pr (ofLetter x) (ofLetter y) with dec x y
    ... | inl refl = inl refl
    ... | inr x!=y = inr λ p → x!=y (ofLetterInjective p)
    pr (ofLetter x) (ofInv y) = inr λ ()
    pr (ofInv x) (ofLetter y) = inr λ ()
    pr (ofInv x) (ofInv y) with dec x y
    ... | inl refl = inl refl
    ... | inr x!=y = inr λ p → x!=y (ofInvInjective p)

freeCompletionEqual : {a : _} {A : Set a} (dec : DecidableSet A) (x y : FreeCompletion A) → Bool
freeCompletionEqual dec x y with DecidableSet.eq (decidableFreeCompletion dec) x y
freeCompletionEqual dec x y | inl x₁ = BoolTrue
freeCompletionEqual dec x y | inr x₁ = BoolFalse

freeCompletionEqualFalse : {a : _} {A : Set a} (dec : DecidableSet A) {x y : FreeCompletion A} → ((x ≡ y) → False) → (freeCompletionEqual dec x y) ≡ BoolFalse
freeCompletionEqualFalse dec {x = x} {y} x!=y with DecidableSet.eq (decidableFreeCompletion dec) x y
freeCompletionEqualFalse dec {x} {y} x!=y | inl x=y = exFalso (x!=y x=y)
freeCompletionEqualFalse dec {x} {y} x!=y | inr _ = refl

freeCompletionEqualFalse' : {a : _} {A : Set a} (dec : DecidableSet A) {x y : FreeCompletion A} → (freeCompletionEqual dec x y) ≡ BoolFalse → (x ≡ y) → False
freeCompletionEqualFalse' dec {x} {y} pr with DecidableSet.eq (decidableFreeCompletion dec) x y
freeCompletionEqualFalse' dec {x} {y} () | inl x₁
freeCompletionEqualFalse' dec {x} {y} pr | inr ans = ans

data ReducedWord {a : _} {A : Set a} (decA : DecidableSet A) : Set a
wordLength : {a : _} {A : Set a} {decA : DecidableSet A} → ReducedWord decA → ℕ
firstLetter : {a : _} {A : Set a} {decA : DecidableSet A} → (w : ReducedWord decA) → (0 <N wordLength w) → FreeCompletion A

data PrependIsValid {a : _} {A : Set a} (decA : DecidableSet A) (w : ReducedWord decA) (l : FreeCompletion A) : Set a where
  wordEmpty : wordLength w ≡ 0 → PrependIsValid decA w l
  wordEnding : (pr : 0 <N wordLength w) → (freeCompletionEqual decA l (freeInverse (firstLetter w pr)) ≡ BoolFalse) → PrependIsValid decA w l

data ReducedWord {a} {A} decA where
  empty : ReducedWord decA
  prependLetter : (letter : FreeCompletion A) → (w : ReducedWord decA) → PrependIsValid decA w letter → ReducedWord decA

firstLetter {a} {A} empty (le x ())
firstLetter {a} {A} (prependLetter letter w x) pr = letter

wordLength {a} {A} empty = 0
wordLength {a} {A} (prependLetter letter w pr) = succ (wordLength w)

data FreeGroupGenerators {a : _} (A : Set a) : Set a where
  χ : A → FreeGroupGenerators A

prependLetterInjective : {a : _} {A : Set a} {decA : DecidableSet A} {x : FreeCompletion A} {w1 w2 : ReducedWord decA} {pr1 : PrependIsValid decA w1 x} {pr2 : PrependIsValid decA w2 x} → prependLetter x w1 pr1 ≡ prependLetter x w2 pr2 → w1 ≡ w2
prependLetterInjective {x = x} {w1} {.w1} {pr1} {.pr1} refl = refl

prependLetterInjective' : {a : _} {A : Set a} {decA : DecidableSet A} {x y : FreeCompletion A} {w1 w2 : ReducedWord decA} {pr1 : PrependIsValid decA w1 x} {pr2 : PrependIsValid decA w2 y} → prependLetter x w1 pr1 ≡ prependLetter y w2 pr2 → x ≡ y
prependLetterInjective' refl = refl

prependLetterRefl : {a : _} {A : Set a} {decA : DecidableSet A} {x : FreeCompletion A} {w : ReducedWord decA} → {pr1 pr2 : PrependIsValid decA w x} → prependLetter x w pr1 ≡ prependLetter x w pr2
prependLetterRefl {a} {A} {decA} {x} {empty} {wordEmpty refl} {wordEmpty refl} = refl
prependLetterRefl {a} {A} {decA} {x} {empty} {wordEmpty refl} {wordEnding (le x₁ ()) x₂}
prependLetterRefl {a} {A} {decA} {x} {empty} {wordEnding (le x₂ ()) x₁} {pr2}
prependLetterRefl {a} {A} {decA} {x} {prependLetter letter w x₁} {wordEmpty ()} {pr2}
prependLetterRefl {a} {A} {decA} {x} {prependLetter letter w x₁} {wordEnding pr x₂} {wordEmpty ()}
prependLetterRefl {a} {A} {decA} {x} {prependLetter letter w x₁} {wordEnding pr2 r2} {wordEnding pr1 r1} rewrite <NRefl pr1 (succIsPositive (wordLength w)) | <NRefl pr2 (succIsPositive (wordLength w)) | reflRefl r1 r2 = refl

badPrepend : {a : _} {A : Set a} {decA : DecidableSet A} {x : A} {w : ReducedWord decA} {pr : PrependIsValid decA w (ofInv x)} → (PrependIsValid decA (prependLetter (ofInv x) w pr) (ofLetter x)) → False
badPrepend (wordEmpty ())
badPrepend {decA = decA} {x = x} (wordEnding pr bad) with DecidableSet.eq (decidableFreeCompletion decA) (ofLetter x) (ofLetter x)
badPrepend {decA = decA} {x} (wordEnding pr ()) | inl x₁
badPrepend {decA = decA} {x} (wordEnding pr bad) | inr pr2 = pr2 refl

badPrepend' : {a : _} {A : Set a} {decA : DecidableSet A} {x : A} {w : ReducedWord decA} {pr : PrependIsValid decA w (ofLetter x)} → (PrependIsValid decA (prependLetter (ofLetter x) w pr) (ofInv x)) → False
badPrepend' (wordEmpty ())
badPrepend' {decA = decA} {x = x} (wordEnding pr x₁) with DecidableSet.eq (decidableFreeCompletion decA) (ofInv x) (ofInv x)
badPrepend' {decA = decA} {x} (wordEnding pr ()) | inl x₂
badPrepend' {decA = decA} {x} (wordEnding pr x₁) | inr pr2 = pr2 refl

freeGroupGenerators : {a : _} (A : Set a) (decA : DecidableSet A) (w : FreeGroupGenerators A) → SymmetryGroupElements (reflSetoid (ReducedWord decA))
freeGroupGenerators A decA (χ x) = sym {f = f} bij
  where
    open DecidableSet decA
    f : ReducedWord decA → ReducedWord decA
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
    bij : SetoidBijection (reflSetoid (ReducedWord decA)) (reflSetoid (ReducedWord decA)) f
    SetoidInjection.wellDefined (SetoidBijection.inj bij) x=y rewrite x=y = refl
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {empty} fx=fy = refl
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofLetter x₁) y pr1} ()
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) y pr1} fx=fy with DecidableSet.eq decA l x
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) empty (wordEmpty x₁)} () | inl l=x
    SetoidInjection.injective (SetoidBijection.inj bij) {empty} {prependLetter (ofInv l) empty (wordEnding (le x ()) x₁)} fx=fy | inl l=x
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
    SetoidSurjection.surjective (SetoidBijection.surj bij) {prependLetter (ofLetter x) empty (wordEnding (le x₂ ()) x₁)} | inl refl
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
