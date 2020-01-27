{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition

module Sets.FinSet.Lemmas where

fneSymmetric : {n : ℕ} → {a b : FinSet (succ n)} → FinNotEquals a b → FinNotEquals b a
fneSymmetric {.1} {.a1} {.b1} (fne2 a1 b1 (inl x)) = fne2 b1 a1 (inr x)
fneSymmetric {.1} {.a1} {.b1} (fne2 a1 b1 (inr x)) = fne2 b1 a1 (inl x)
fneSymmetric {.(succ (succ _))} {.fzero} {b} (fneN .fzero b (inl (inl (refl ,, snd)))) = fneN b fzero (inl (inr (snd ,, refl)))
fneSymmetric {.(succ (succ _))} {a} {.fzero} (fneN a .fzero (inl (inr (fst ,, refl)))) = fneN fzero a (inl (inl (refl ,, fst)))
fneSymmetric {.(succ (succ _))} {a} {b} (fneN a b (inr ((fst ,, snd) , record { one = o ; two = p ; three = q }))) = fneN b a (inr ((snd ,, fst) , record { one = p ; two = o ; three = fneSymmetric q }))

private
  underlyingProof : {l m : _} {L : Set l} {pr : L → Set m} → (a : Sg L pr) → pr (underlying a)
  underlyingProof (a , b) = b

finSetNotEquals : {n : ℕ} → {a b : FinSet (succ n)} → (a ≡ b → False) → FinNotEquals {n} a b
finSetNotEquals {zero} {fzero} {fzero} pr = exFalso (pr refl)
finSetNotEquals {zero} {fzero} {fsucc ()} pr
finSetNotEquals {zero} {fsucc ()} {b} pr
finSetNotEquals {succ zero} {fzero} {fzero} pr = exFalso (pr refl)
finSetNotEquals {succ zero} {fzero} {fsucc fzero} pr = fne2 fzero (fsucc fzero) (inl (refl ,, refl))
finSetNotEquals {succ zero} {fzero} {fsucc (fsucc ())} pr
finSetNotEquals {succ zero} {fsucc fzero} {fzero} pr = fne2 (fsucc fzero) fzero (inr (refl ,, refl))
finSetNotEquals {succ zero} {fsucc fzero} {fsucc fzero} pr = exFalso (pr refl)
finSetNotEquals {succ zero} {fsucc fzero} {fsucc (fsucc ())} pr
finSetNotEquals {succ zero} {fsucc (fsucc ())}
finSetNotEquals {succ (succ n)} {fzero} {fzero} pr = exFalso (pr refl)
finSetNotEquals {succ (succ n)} {fzero} {fsucc b} pr = fneN fzero (fsucc b) (inl (inl (refl ,, (b , refl))))
finSetNotEquals {succ (succ n)} {fsucc a} {fzero} pr = fneN (fsucc a) fzero (inl (inr ((a , refl) ,, refl)))
finSetNotEquals {succ (succ n)} {fsucc a} {fsucc b} pr = fneN (fsucc a) (fsucc b) (inr ans)
  where
    q : a ≡ b → False
    q refl = pr refl
    t : FinNotEquals {succ n} a b
    t = finSetNotEquals {succ n} {a} {b} q
    ans : Sg (FinSet (succ (succ n)) && FinSet (succ (succ n))) (λ x → (fsucc a ≡ fsucc (_&&_.fst x)) & fsucc b ≡ fsucc (_&&_.snd x) & FinNotEquals (_&&_.fst x) (_&&_.snd x))
    ans with t
    ans | fne2 .fzero .(fsucc fzero) (inl (refl ,, refl)) = (a ,, b) , record { one = refl ; two = refl ; three = fne2 fzero (fsucc fzero) (inl (refl ,, refl)) }
    ans | fne2 .(fsucc fzero) .fzero (inr (refl ,, refl)) = (a ,, b) , record { one = refl ; two = refl ; three = fne2 (fsucc fzero) fzero (inr (refl ,, refl)) }
    ans | fneN a b _ = (a ,, b) , record { one = refl ; two = refl ; three = t }

fzeroNotFsucc : {n : ℕ} → {a : _} → fzero ≡ fsucc {succ n} a → False
fzeroNotFsucc ()

finSetNotEqualsSame : {n : ℕ} → {a : FinSet (succ n)} → FinNotEquals a a → False
finSetNotEqualsSame {.1} {fzero} (fne2 .fzero .fzero (inl (fst ,, ())))
finSetNotEqualsSame {.1} {fzero} (fne2 .fzero .fzero (inr (fst ,, ())))
finSetNotEqualsSame {.(succ (succ _))} {fzero} (fneN .fzero .fzero (inl (inl (refl ,, (a , ())))))
finSetNotEqualsSame {.(succ (succ _))} {fzero} (fneN .fzero .fzero (inl (inr ((a , ()) ,, refl))))
finSetNotEqualsSame {.(succ (succ _))} {fzero} (fneN .fzero .fzero (inr ((fst ,, snd) , record { one = () ; two = p ; three = q })))
finSetNotEqualsSame {.1} {fsucc a} (fne2 .(fsucc a) .(fsucc a) (inl (() ,, snd)))
finSetNotEqualsSame {.1} {fsucc a} (fne2 .(fsucc a) .(fsucc a) (inr (() ,, snd)))
finSetNotEqualsSame {.(succ (succ _))} {fsucc a} (fneN .(fsucc a) .(fsucc a) (inl (inl (() ,, snd))))
finSetNotEqualsSame {.(succ (succ _))} {fsucc a} (fneN .(fsucc a) .(fsucc a) (inl (inr (fst ,, ()))))
finSetNotEqualsSame {.(succ (succ _))} {fsucc a} (fneN .(fsucc a) .(fsucc a) (inr ((.a ,, .a) , record { one = refl ; two = refl ; three = q }))) = finSetNotEqualsSame q

finNotEqualsFsucc : {n : ℕ} → {a b : FinSet (succ n)} → FinNotEquals (fsucc a) (fsucc b) → FinNotEquals a b
finNotEqualsFsucc {.0} {a} {b} (fne2 .(fsucc a) .(fsucc b) (inl (() ,, snd)))
finNotEqualsFsucc {.0} {a} {b} (fne2 .(fsucc a) .(fsucc b) (inr (() ,, snd)))
finNotEqualsFsucc {n} {a} {b} (fneN .(fsucc a) .(fsucc b) (inl (inl (() ,, snd))))
finNotEqualsFsucc {n} {a} {b} (fneN .(fsucc a) .(fsucc b) (inl (inr (fst ,, ()))))
finNotEqualsFsucc {n} {a} {b} (fneN .(fsucc a) .(fsucc b) (inr ((fst ,, snd) , prf))) = identityOfIndiscernablesRight FinNotEquals ans (equalityCommutative b=snd)
  where
    a=fst : a ≡ fst
    a=fst = fsuccInjective (_&_&_.one prf)
    b=snd : b ≡ snd
    b=snd = fsuccInjective (_&_&_.two prf)
    ans : FinNotEquals a snd
    ans = identityOfIndiscernablesLeft FinNotEquals (_&_&_.three prf) (equalityCommutative a=fst)

finSetNotEquals' : {n : ℕ} → {a b : FinSet (succ n)} → FinNotEquals a b → (a ≡ b → False)
finSetNotEquals' {n} {a} {.a} fne refl = finSetNotEqualsSame fne

finset0Empty : FinSet zero → False
finset0Empty ()

finset1OnlyOne : (a b : FinSet 1) → a ≡ b
finset1OnlyOne fzero fzero = refl
finset1OnlyOne fzero (fsucc ())
finset1OnlyOne (fsucc ()) b

intoSmaller : {n m : ℕ} → .(n <N m) → (FinSet n → FinSet m)
intoSmaller {zero} {m} n<m = t
  where
    t : FinSet 0 → FinSet m
    t ()
intoSmaller {succ n} {zero} ()
intoSmaller {succ n} {succ m} n<m with intoSmaller (canRemoveSuccFrom<N n<m)
intoSmaller {succ n} {succ m} n<m | prev = t
  where
    t : FinSet (succ n) → FinSet (succ m)
    t fzero = fzero
    t (fsucc arg) = fsucc (prev arg)

intoSmallerInj : {n m : ℕ} → (n<m : n <N m) → Injection (intoSmaller n<m)
intoSmallerInj {zero} {zero} (le x ())
intoSmallerInj {zero} {succ m} n<m = inj
  where
    t : FinSet 0 → FinSet (succ m)
    t ()
    inj : {x y : FinSet zero} → intoSmaller (succIsPositive m) x ≡ intoSmaller (succIsPositive m) y → x ≡ y
    inj {()} {y}
intoSmallerInj {succ n} {zero} ()
intoSmallerInj {succ n} {succ m} n<m with intoSmallerInj (canRemoveSuccFrom<N n<m)
intoSmallerInj {succ n} {succ m} n<m | prevInj = inj
  where
    inj : Injection (intoSmaller n<m)
    inj {fzero} {fzero} pr = refl
    inj {fzero} {fsucc y} ()
    inj {fsucc x} {fzero} ()
    inj {fsucc x} {fsucc y} pr = applyEquality fsucc (prevInj (fsuccInjective pr))

toNat : {n : ℕ} → (a : FinSet n) → ℕ
toNat {.(succ _)} fzero = 0
toNat {.(succ _)} (fsucc a) = succ (toNat a)

toNatSmaller : {n : ℕ} → (a : FinSet n) → toNat a <N n
toNatSmaller {zero} ()
toNatSmaller {succ n} fzero = succIsPositive n
toNatSmaller {succ n} (fsucc a) = succPreservesInequality (toNatSmaller a)

ofNat : {n : ℕ} → (m : ℕ) → .(m <N n) → FinSet n
ofNat {zero} zero ()
ofNat {succ n} zero m<n = fzero
ofNat {zero} (succ m) ()
ofNat {succ n} (succ m) m<n = fsucc (ofNat {n} m (canRemoveSuccFrom<N m<n))

ofNatInjective : {n : ℕ} → (x y : ℕ) → .(pr : x <N n) → .(pr2 : y <N n) → ofNat x pr ≡ ofNat y pr2 → x ≡ y
ofNatInjective {zero} zero zero () y<n pr
ofNatInjective {zero} zero (succ y) () y<n pr
ofNatInjective {zero} (succ x) zero x<n () pr
ofNatInjective {zero} (succ x) (succ y) () y<n pr
ofNatInjective {succ n} zero zero x<n y<n pr = refl
ofNatInjective {succ n} zero (succ y) x<n y<n ()
ofNatInjective {succ n} (succ x) zero x<n y<n ()
ofNatInjective {succ n} (succ x) (succ y) x<n y<n pr = applyEquality succ (ofNatInjective x y (canRemoveSuccFrom<N x<n) (canRemoveSuccFrom<N y<n) (fsuccInjective pr))

toNatInjective : {n : ℕ} → (x y : FinSet n) → toNat x ≡ toNat y → x ≡ y
toNatInjective fzero fzero pr = refl
toNatInjective (fsucc x) (fsucc y) pr = applyEquality fsucc (toNatInjective x y (succInjective pr))

toNatOfNat : {n : ℕ} → (a : ℕ) → (a<n : a <N n) → toNat (ofNat a a<n) ≡ a
toNatOfNat {zero} zero (le x ())
toNatOfNat {zero} (succ a) (le x ())
toNatOfNat {succ n} zero a<n = refl
toNatOfNat {succ n} (succ a) a<n = applyEquality succ (toNatOfNat a (canRemoveSuccFrom<N a<n))

intoSmallerLemm : {n m : ℕ} → {n<m : n <N (succ m)} → {m<sm : m <N succ m} → (b : FinSet n) → intoSmaller n<m b ≡ ofNat m m<sm → False
intoSmallerLemm {.(succ _)} {m} {n<m} fzero pr with intoSmaller (canRemoveSuccFrom<N n<m)
intoSmallerLemm {.(succ _)} {zero} {n<m} fzero refl | bl = zeroNeverGreater (canRemoveSuccFrom<N n<m)
intoSmallerLemm {.(succ _)} {succ m} {n<m} fzero () | bl
intoSmallerLemm {.(succ _)} {m} {n<m} (fsucc b) pr with inspect (intoSmaller (canRemoveSuccFrom<N n<m))
intoSmallerLemm {.(succ _)} {zero} {n<m} (fsucc b) pr | bl with≡ _ = zeroNeverGreater (canRemoveSuccFrom<N n<m)
intoSmallerLemm {.(succ _)} {succ m} {n<m} {m<sm} (fsucc b) pr | bl with≡ p = intoSmallerLemm {n<m = canRemoveSuccFrom<N n<m} {m<sm = canRemoveSuccFrom<N m<sm} b (fsuccInjective pr)

intoSmallerNotSurj : {n m : ℕ} → {n<m : n <N m} → Surjection (intoSmaller n<m) → False
intoSmallerNotSurj {n} {zero} {le x ()} property
intoSmallerNotSurj {zero} {succ zero} {n<m} property with property fzero
... | () , _
intoSmallerNotSurj {succ n} {succ zero} {n<m} property = zeroNeverGreater (canRemoveSuccFrom<N n<m)
intoSmallerNotSurj {0} {succ (succ m)} {n<m} property with property fzero
... | () , _
intoSmallerNotSurj {succ n} {succ (succ m)} {n<m} property = problem
  where
    notHit : FinSet (succ (succ m))
    notHit = ofNat (succ m) (le zero refl)
    hitting : Sg (FinSet (succ n)) (λ i → intoSmaller n<m i ≡ notHit)
    hitting = property notHit
    problem : False
    problem with hitting
    ... | a , pr = intoSmallerLemm {succ n} {succ m} {n<m} {le 0 refl} a pr

finsetDecidableEquality : {n : ℕ} → (x y : FinSet n) → (x ≡ y) || ((x ≡ y) → False)
finsetDecidableEquality fzero fzero = inl refl
finsetDecidableEquality fzero (fsucc y) = inr λ ()
finsetDecidableEquality (fsucc x) fzero = inr λ ()
finsetDecidableEquality (fsucc x) (fsucc y) with finsetDecidableEquality x y
finsetDecidableEquality (fsucc x) (fsucc y) | inl pr rewrite pr = inl refl
finsetDecidableEquality (fsucc x) (fsucc y) | inr pr = inr (λ f → pr (fsuccInjective f))

subInjection : {n : ℕ} → {f : FinSet (succ (succ n)) → FinSet (succ (succ n))} → Injection f → (FinSet (succ n) → FinSet (succ n))
subInjection {n} {f} inj x with inspect (f (fsucc x))
subInjection {f = f} inj x | fzero with≡ _ with inspect (f fzero)
subInjection {f = f} inj x | fzero with≡ pr | fzero with≡ pr2 = exFalso (fzeroNotFsucc (inj (transitivity pr2 (equalityCommutative pr))))
subInjection {f = f} inj x | fzero with≡ _ | fsucc bl with≡ _ = bl
subInjection {f = f} inj x | fsucc bl with≡ _ = bl

subInjIsInjective : {n : ℕ} → {f : FinSet (succ (succ n)) → FinSet (succ (succ n))} → (inj : Injection f) → Injection (subInjection inj)
subInjIsInjective {f = f} inj {x} {y} pr with inspect (f (fsucc x))
subInjIsInjective {f = f} inj {x} {y} pr | fzero with≡ _ with inspect (f (fzero))
subInjIsInjective {f = f} inj {x} {y} pr | fzero with≡ pr1 | fzero with≡ pr2 = exFalso (fzeroNotFsucc (inj (transitivity pr2 (equalityCommutative pr1))))
subInjIsInjective {f = f} inj {x} {y} pr | fzero with≡ pr1 | fsucc bl with≡ _ with inspect (f (fsucc y))
subInjIsInjective {f = f} inj {x} {y} pr | fzero with≡ pr1 | fsucc bl with≡ _ | fzero with≡ x₁ with inspect (f (fzero))
subInjIsInjective {f = f} inj {x} {y} pr | fzero with≡ pr1 | fsucc bl with≡ _ | fzero with≡ x1 | fzero with≡ x2 = exFalso (fzeroNotFsucc (inj (transitivity x2 (equalityCommutative x1))))
subInjIsInjective {f = f} inj {x} {y} refl | fzero with≡ pr1 | fsucc .bl2 with≡ _ | fzero with≡ x1 | fsucc bl2 with≡ _ = fsuccInjective (inj (transitivity pr1 (equalityCommutative x1)))
subInjIsInjective {f = f} inj {x} {y} refl | fzero with≡ pr1 | fsucc .bl2 with≡ pr2 | fsucc bl2 with≡ pr3 = exFalso (fzeroNotFsucc (inj (transitivity pr2 (equalityCommutative pr3))))
subInjIsInjective {f = f} inj {x} {y} pr | fsucc bl with≡ _ with inspect (f (fsucc y))
subInjIsInjective {f = f} inj {x} {y} pr | fsucc bl with≡ _ | fzero with≡ x₁ with inspect (f fzero)
subInjIsInjective {f = f} inj {x} {y} pr | fsucc bl with≡ _ | fzero with≡ x1 | fzero with≡ x2 = exFalso (fzeroNotFsucc (inj (transitivity x2 (equalityCommutative x1))))
subInjIsInjective {f = f} inj {x} {y} refl | fsucc .bl2 with≡ x1 | fzero with≡ x₁ | fsucc bl2 with≡ x2 = exFalso (fzeroNotFsucc (inj (transitivity x2 (equalityCommutative x1))))
subInjIsInjective {f = f} inj {x} {y} refl | fsucc .y1 with≡ pr1 | fsucc y1 with≡ pr2 = fsuccInjective (inj (transitivity pr1 (equalityCommutative pr2)))

onepointBij : (f : FinSet 1 → FinSet 1) → Bijection f
Bijection.inj (onepointBij f) {x} {y} _ = finset1OnlyOne x y
Bijection.surj (onepointBij f) fzero with inspect (f fzero)
... | fzero with≡ pr = fzero , pr
... | fsucc () with≡ _
Bijection.surj (onepointBij f) (fsucc ())

nopointBij : (f : FinSet 0 → FinSet 0) → Bijection f
Bijection.inj (nopointBij f) {()}
Bijection.surj (nopointBij f) ()

private
  flip : {n : ℕ} → (f : FinSet (succ n) → FinSet (succ n)) → FinSet (succ n) → FinSet (succ n)
  flip {n} f fzero = f fzero
  flip {n} f (fsucc a) with inspect (f fzero)
  flip {n} f (fsucc a) | fzero with≡ x = fsucc a
  flip {n} f (fsucc a) | fsucc y with≡ x with finsetDecidableEquality a y
  flip {n} f (fsucc a) | fsucc y with≡ x | inl a=y = fzero
  flip {n} f (fsucc a) | fsucc y with≡ x | inr a!=y = fsucc a

  flipSwapsF0 : {n : ℕ} → {f : FinSet (succ n) → FinSet (succ n)} → (flip f (f fzero)) ≡ fzero
  flipSwapsF0 {zero} {f} with inspect (f fzero)
  flipSwapsF0 {zero} {f} | fzero with≡ x rewrite x = x
  flipSwapsF0 {zero} {f} | fsucc () with≡ x
  flipSwapsF0 {succ n} {f = f} with inspect (f fzero)
  flipSwapsF0 {succ n} {f = f} | fzero with≡ pr rewrite pr = pr
  flipSwapsF0 {succ n} {f = f} | fsucc b with≡ pr rewrite pr = ans
    where
      ans : flip f (fsucc b) ≡ fzero
      ans with inspect (f fzero)
      ans | fzero with≡ x = exFalso (fzeroNotFsucc (transitivity (equalityCommutative x) pr))
      ans | fsucc y with≡ x with finsetDecidableEquality b y
      ans | fsucc y with≡ x | inl b=y = refl
      ans | fsucc y with≡ x | inr b!=y = exFalso (b!=y (fsuccInjective (transitivity (equalityCommutative pr) x)))

  flipSwapsZero : {n : ℕ} → {f : FinSet (succ n) → FinSet (succ n)} → (flip f fzero) ≡ f fzero
  flipSwapsZero {n} {f} = refl

  flipMaintainsEverythingElse : {n : ℕ} → {f : FinSet (succ n) → FinSet (succ n)} → (x : FinSet n) → ((fsucc x ≡ f fzero) → False) → flip f (fsucc x) ≡ fsucc x
  flipMaintainsEverythingElse {n} {f} x x!=f0 with inspect (f fzero)
  flipMaintainsEverythingElse {n} {f} x x!=f0 | fzero with≡ pr = refl
  flipMaintainsEverythingElse {n} {f} x x!=f0 | fsucc bl with≡ pr with finsetDecidableEquality x bl
  flipMaintainsEverythingElse {n} {f} x x!=f0 | fsucc bl with≡ pr | inl x=bl = exFalso (x!=f0 (transitivity (applyEquality fsucc x=bl) (equalityCommutative pr)))
  flipMaintainsEverythingElse {n} {f} x x!=f0 | fsucc bl with≡ pr | inr x!=bl = refl

  bijFlip : {n : ℕ} → {f : FinSet (succ n) → FinSet (succ n)} → Bijection (flip f)
  bijFlip {zero} {f} = onepointBij (flip f)
  Bijection.inj (bijFlip {succ n} {f}) {fzero} {fzero} flx=fly = refl
  Bijection.inj (bijFlip {succ n} {f}) {fzero} {fsucc y} flx=fly with inspect (f fzero)
  Bijection.inj (bijFlip {succ n} {f}) {fzero} {fsucc y} flx=fly | fzero with≡ x rewrite x = exFalso (fzeroNotFsucc flx=fly)
  Bijection.inj (bijFlip {succ n} {f}) {fzero} {fsucc y} flx=fly | fsucc f0 with≡ x with finsetDecidableEquality y f0
  Bijection.inj (bijFlip {succ n} {f}) {fzero} {fsucc y} flx=fly | fsucc f0 with≡ x | inl x₁ = exFalso (fzeroNotFsucc (transitivity (equalityCommutative flx=fly) x))
  Bijection.inj (bijFlip {succ n} {f}) {fzero} {fsucc y} flx=fly | fsucc f0 with≡ x | inr pr = exFalso (pr (fsuccInjective (transitivity (equalityCommutative flx=fly) x)))
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fzero} flx=fly with inspect (f fzero)
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fzero} flx=fly | fzero with≡ pr = transitivity flx=fly pr
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fzero} flx=fly | fsucc f0 with≡ x₁ with finsetDecidableEquality x f0
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fzero} flx=fly | fsucc f0 with≡ pr | inl x₂ = exFalso (fzeroNotFsucc (transitivity flx=fly pr))
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fzero} flx=fly | fsucc f0 with≡ x1 | inr x!=f0 = exFalso (x!=f0 (fsuccInjective (transitivity flx=fly x1)))
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} flx=fly with inspect (f fzero)
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} flx=fly | fzero with≡ x₁ = flx=fly
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} flx=fly | fsucc f0 with≡ x₁ with finsetDecidableEquality y f0
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} flx=fly | fsucc f0 with≡ x₁ | inl y=f0 with finsetDecidableEquality x f0
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} flx=fly | fsucc f0 with≡ x₁ | inl y=f0 | inl x=f0 = applyEquality fsucc (transitivity x=f0 (equalityCommutative y=f0))
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} () | fsucc f0 with≡ x₁ | inl y=f0 | inr x!=f0
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} flx=fly | fsucc f0 with≡ x₁ | inr y!=f0 with finsetDecidableEquality x f0
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} () | fsucc f0 with≡ x₁ | inr y!=f0 | inl x=f0
  Bijection.inj (bijFlip {succ n} {f}) {fsucc x} {fsucc y} flx=fly | fsucc f0 with≡ x₁ | inr y!=f0 | inr x!=f0 = flx=fly
  Bijection.surj (bijFlip {succ n} {f}) fzero = f fzero , flipSwapsF0 {f = f}
  Bijection.surj (bijFlip {succ n} {f}) (fsucc b) with inspect (f fzero)
  Bijection.surj (bijFlip {succ n} {f}) (fsucc b) | fzero with≡ x = fsucc b , flipMaintainsEverythingElse {f = f} b λ pr → fzeroNotFsucc (transitivity (equalityCommutative x) (equalityCommutative pr))
  Bijection.surj (bijFlip {succ n} {f}) (fsucc b) | fsucc y with≡ x with finsetDecidableEquality y b
  Bijection.surj (bijFlip {succ n} {f}) (fsucc b) | fsucc y with≡ x | inl y=b = fzero , transitivity x (applyEquality fsucc y=b)
  Bijection.surj (bijFlip {succ n} {f}) (fsucc b) | fsucc y with≡ x | inr y!=b = fsucc b , flipMaintainsEverythingElse {f = f} b λ pr → y!=b (fsuccInjective (transitivity (equalityCommutative x) (equalityCommutative pr)))

injectionIsBijectionFinset : {n : ℕ} → {f : FinSet n → FinSet n} → Injection f → Bijection f
injectionIsBijectionFinset {zero} {f} inj = record { inj = inj ; surj = λ () }
injectionIsBijectionFinset {succ zero} {f} inj = record { inj = inj ; surj = ans }
  where
    ans : (b : FinSet (succ zero)) → Sg (FinSet (succ zero)) (λ a → f a ≡ b)
    ans fzero with inspect (f fzero)
    ans fzero | fzero with≡ x = fzero , x
    ans fzero | fsucc () with≡ x
    ans (fsucc ())
injectionIsBijectionFinset {succ (succ n)} {f} inj with injectionIsBijectionFinset {succ n} (subInjIsInjective inj)
... | sb = ans
  where
    subSurj : Surjection (subInjection inj)
    subSurj = Bijection.surj sb

    tweakedF : FinSet (succ (succ n)) → FinSet (succ (succ n))
    tweakedF fzero = fzero
    tweakedF (fsucc x) = fsucc (subInjection inj x)

    tweakedBij : Bijection tweakedF
    Bijection.inj tweakedBij {fzero} {fzero} f'x=f'y = refl
    Bijection.inj tweakedBij {fzero} {fsucc y} ()
    Bijection.inj tweakedBij {fsucc x} {fzero} ()
    Bijection.inj tweakedBij {fsucc x} {fsucc y} f'x=f'y = applyEquality fsucc ((subInjIsInjective inj) (fsuccInjective f'x=f'y))
    Bijection.surj tweakedBij fzero = fzero , refl
    Bijection.surj tweakedBij (fsucc b) with subSurj b
    ... | ans , prop = fsucc ans , applyEquality fsucc prop

    compBij : Bijection (λ i → flip f (tweakedF i))
    compBij = bijectionComp tweakedBij bijFlip

    undoTweakMakesF : {x : FinSet (succ (succ n))} → flip f (tweakedF x) ≡ f x
    undoTweakMakesF {fzero} = refl
    undoTweakMakesF {fsucc x} with inspect (f fzero)
    undoTweakMakesF {fsucc x} | fzero with≡ x₁ with inspect (f (fsucc x))
    undoTweakMakesF {fsucc x} | fzero with≡ x₁ | fzero with≡ x₂ with inspect (f fzero)
    undoTweakMakesF {fsucc x} | fzero with≡ x₁ | fzero with≡ x2 | fzero with≡ x3 = exFalso (fzeroNotFsucc (inj (transitivity x3 (equalityCommutative x2))))
    undoTweakMakesF {fsucc x} | fzero with≡ x1 | fzero with≡ x2 | fsucc y with≡ x3 = exFalso (fzeroNotFsucc (inj (transitivity x1 (equalityCommutative x2))))
    undoTweakMakesF {fsucc x} | fzero with≡ x1 | fsucc y with≡ x2 = equalityCommutative x2
    undoTweakMakesF {fsucc x} | fsucc y with≡ x₁ with inspect (f (fsucc x))
    undoTweakMakesF {fsucc x} | fsucc y with≡ x₁ | fzero with≡ x₂ with inspect (f fzero)
    undoTweakMakesF {fsucc x} | fsucc y with≡ x₁ | fzero with≡ x2 | fzero with≡ x3 = exFalso (fzeroNotFsucc (inj (transitivity x3 (equalityCommutative x2))))
    undoTweakMakesF {fsucc x} | fsucc y with≡ x₁ | fzero with≡ x₂ | fsucc pr with≡ x₃ with finsetDecidableEquality pr y
    undoTweakMakesF {fsucc x} | fsucc y with≡ x₁ | fzero with≡ x2 | fsucc pr with≡ x₃ | inl x₄ = equalityCommutative x2
    undoTweakMakesF {fsucc x} | fsucc y with≡ x1 | fzero with≡ x₂ | fsucc pr with≡ x3 | inr pr!=y = exFalso (pr!=y (fsuccInjective (transitivity (equalityCommutative x3) x1)))
    undoTweakMakesF {fsucc x} | fsucc y with≡ x₁ | fsucc thi with≡ x₂ with finsetDecidableEquality thi y
    undoTweakMakesF {fsucc x} | fsucc .thi with≡ x1 | fsucc thi with≡ x2 | inl refl = exFalso false
      where
        p : f fzero ≡ f (fsucc x)
        p = transitivity x1 (equalityCommutative x2)
        q : fzero ≡ fsucc x
        q = inj p
        false : False
        false = fzeroNotFsucc q
    undoTweakMakesF {fsucc x} | fsucc y with≡ x₁ | fsucc thi with≡ x2 | inr thi!=y = equalityCommutative x2

    ans : Bijection f
    ans = bijectionPreservedUnderExtensionalEq compBij undoTweakMakesF

pigeonhole : {n m : ℕ} → (m <N n) → {f : FinSet n → FinSet m} → Injection f → False
pigeonhole {zero} {zero} () {f} property
pigeonhole {zero} {succ m} () {f} property
pigeonhole {succ n} {zero} m<n {f} property = finset0Empty (f fzero)
pigeonhole {succ zero} {succ m} m<n {f} property with canRemoveSuccFrom<N m<n
pigeonhole {succ zero} {succ m} m<n {f} property | le x ()
pigeonhole {succ (succ n)} {succ zero} m<n {f} property = fzeroNotFsucc (property (transitivity f0 (equalityCommutative f1)))
  where
    f0 : f (fzero) ≡ fzero
    f0 with inspect (f fzero)
    ... | fzero with≡ x = x
    ... | fsucc () with≡ _
    f1 : f (fsucc fzero) ≡ fzero
    f1 with inspect (f (fsucc fzero))
    ... | fzero with≡ x = x
    ... | fsucc () with≡ _
pigeonhole {succ (succ n)} {succ (succ m)} m<n {f} injF = intoSmallerNotSurj {_}{_} {m<n} surj
  where
    inj : Injection ((intoSmaller m<n) ∘ f)
    inj = injComp injF (intoSmallerInj m<n)
    bij : Bijection ((intoSmaller m<n) ∘ f)
    bij = injectionIsBijectionFinset inj
    surj : Surjection (intoSmaller m<n)
    surj = compSurjLeftSurj (Bijection.surj bij)

--surjectionIsBijectionFinset : {n : ℕ} → {f : FinSet n → FinSet n} → Surjection f → Bijection f
--surjectionIsBijectionFinset {zero} {f} surj = nopointBij f
--surjectionIsBijectionFinset {succ zero} {f} surj = onepointBij f
--surjectionIsBijectionFinset {succ (succ n)} {f} record { property = property } = {!!}

ofNatToNat : {n : ℕ} → (a : FinSet n) → ofNat (toNat a) (toNatSmaller a) ≡ a
ofNatToNat {zero} ()
ofNatToNat {succ n} fzero = refl
ofNatToNat {succ n} (fsucc a) = applyEquality fsucc (ofNatToNat a)
