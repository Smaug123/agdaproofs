{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

open import Boolean.Definition
open import Setoids.Setoids
open import Setoids.Subset
open import Setoids.Functions.Definition
open import LogicalFormulae
open import Functions.Definition
open import Lists.Lists

module LectureNotes.MetAndTop.Chapter1 where

PowerSet : {a : _} (A : Set a) → {b : _} → Set (a ⊔ lsuc b)
PowerSet A {b} = A → Set b

equality : {a b c : _} (A : Set a) → PowerSet A {b} → PowerSet A {c} → Set (a ⊔ b ⊔ c)
equality A x y = (z : A) → (x z → y z) && (y z → x z)

trans : {a b c d : _} {A : Set a} → {x : PowerSet A {b}} {y : PowerSet A {c}} {z : PowerSet A {d}} → equality A x y → equality A y z → equality A x z
trans {x} {y} {z} x=y y=z i with x=y i
... | r ,, s with y=z i
... | t ,, u = (λ z → t (r z)) ,, λ z → s (r (_&&_.snd (x=y i) (u z)))

symm : {a b c : _} {A : Set a} → {x : PowerSet A {b}} {y : PowerSet A {c}} → equality A x y → equality A y x
symm x=y i with x=y i
... | r ,, s = s ,, r

reflex : {a b : _} {A : Set a} → (x : PowerSet A {b}) → equality A x x
reflex x i = (λ z → z) ,, λ z → z

mapPower : {a b c : _} {A : Set a} {B : Set b} (f : A → B) → PowerSet B {c} → PowerSet A {c}
mapPower f p a = p (f a)

mapF : {a b c : _} {A : Set a} {B : Set b} (f : A → B) → PowerSet A {c} → PowerSet B {_}
mapF {A = A} f p b = Sg A (λ a → (p a) && (f a ≡ b))

singleton : {a b : _} {A : Set a} → (decidableEquality : (x y : A) → (x ≡ y) || ((x ≡ y) → False)) → A → PowerSet A {b}
singleton decidable a n with decidable a n
singleton decidable a n | inl x = True'
singleton decidable a n | inr x = False'

intersection : {a b c : _} {A : Set a} {B : Set b} (sets : A → PowerSet B {c}) → PowerSet B {a ⊔ c}
intersection {A = A} sets x = (a : A) → (sets a) x

union : {a b c : _} {A : Set a} {B : Set b} (sets : A → PowerSet B {c}) → PowerSet B {a ⊔ c}
union {A = A} sets x = Sg A λ i → sets i x

complement : {a b : _} {A : Set a} → (x : PowerSet A {b}) → PowerSet A
complement x t = x t → False

emptySet : {a b : _} (A : Set a) → PowerSet A {b}
emptySet A x = False'

decideIt : {a b : _} {A : Set a} → {f : A → Set b} → ((x : A) → (f x) || ((f x) → False)) → A → Set _
decideIt decide a with decide a
decideIt decide a | inl x = True
decideIt decide a | inr x = False

fromExtension : {a : _} {A : Set a} → ((x y : A) → (x ≡ y) || ((x ≡ y) → False)) → List A → PowerSet A
fromExtension decideEquality l = decideIt {f = contains l} (containsDecidable decideEquality l)

private

  data !1234 : Set where
    !1 : !1234
    !2 : !1234
    !3 : !1234
    !4 : !1234

  decidable1234 : (x y : !1234) → (x ≡ y) || ((x ≡ y) → False)
  decidable1234 !1 !1 = inl refl
  decidable1234 !1 !2 = inr (λ ())
  decidable1234 !1 !3 = inr (λ ())
  decidable1234 !1 !4 = inr (λ ())
  decidable1234 !2 !1 = inr (λ ())
  decidable1234 !2 !2 = inl refl
  decidable1234 !2 !3 = inr (λ ())
  decidable1234 !2 !4 = inr (λ ())
  decidable1234 !3 !1 = inr (λ ())
  decidable1234 !3 !2 = inr (λ ())
  decidable1234 !3 !3 = inl refl
  decidable1234 !3 !4 = inr (λ ())
  decidable1234 !4 !1 = inr (λ ())
  decidable1234 !4 !2 = inr (λ ())
  decidable1234 !4 !3 = inr (λ ())
  decidable1234 !4 !4 = inl refl

  f : !1234 → !1234
  f !1 = !1
  f !2 = !1
  f !3 = !4
  f !4 = !3

  exercise1'1i1 : {b : _} → equality {b = b} !1234 (mapPower f (singleton decidable1234 !1)) (fromExtension decidable1234 (!1 :: !2 :: []))
  exercise1'1i1 !1 = (λ x → record {}) ,, (λ x → record {})
  exercise1'1i1 !2 = (λ x → record {}) ,, (λ x → record {})
  exercise1'1i1 !3 = (λ ()) ,, (λ ())
  exercise1'1i1 !4 = (λ ()) ,, λ ()

  exercise1'1i2 : {b : _} → equality {b = b} !1234 (mapPower f (singleton decidable1234 !2)) (λ _ → False)
  exercise1'1i2 !1 = (λ ()) ,, λ ()
  exercise1'1i2 !2 = (λ ()) ,, (λ ())
  exercise1'1i2 !3 = (λ ()) ,, (λ ())
  exercise1'1i2 !4 = (λ ()) ,, (λ ())

  exercise1'1i3 : equality !1234 (mapPower f (fromExtension decidable1234 (!3 :: !4 :: []))) (fromExtension decidable1234 (!3 :: !4 :: []))
  exercise1'1i3 !1 = (λ x → x) ,, (λ x → x)
  exercise1'1i3 !2 = (λ x → x) ,, (λ x → x)
  exercise1'1i3 !3 = (λ x → record {}) ,, (λ x → record {})
  exercise1'1i3 !4 = (λ x → record {}) ,, (λ x → record {})

  exercise1'1ii1 : {a b c t : _} {A : Set a} {B : Set b} {T : Set t} → (f : A → B) → (sets : T → PowerSet B {c}) → equality A (mapPower f (union sets)) (union λ x → mapPower f (sets x))
  exercise1'1ii1 f sets i = (λ x → x) ,, (λ x → x)

  exercise1'1ii2 : {a b c t : _} {A : Set a} {B : Set b} {T : Set t} → (f : A → B) → (sets : T → PowerSet B {c}) → equality A (mapPower f (intersection sets)) (intersection λ x → mapPower f (sets x))
  exercise1'1ii2 f sets i = (λ x → x) ,, (λ x → x)

  exercise1'1ii3 : {a b : _} {A : Set a} {B : Set b} → (f : A → B) → equality A (mapPower f (λ i → True)) (λ i → True)
  exercise1'1ii3 f = λ z → (λ x → record {}) ,, (λ x → record {})

  exercise1'1ii4 : {a b c : _} {A : Set a} {B : Set b} → (f : A → B) → equality A (mapPower f (emptySet {b = c} B)) (emptySet A)
  exercise1'1ii4 f = λ z → (λ x → x) ,, (λ x → x)

  exercise1'1ii5 : {a b c : _} {A : Set a} {B : Set b} → (f : A → B) → (u : PowerSet B {c}) → equality A (mapPower f (complement u)) (complement (mapPower f u))
  exercise1'1ii5 f u z = (λ x → x) ,, (λ x → x)

  exercise1'1iii1 : {a b c t : _} {A : Set a} {B : Set b} {T : Set t} → (f : A → B) (sets : T → PowerSet A {c}) → equality B (mapF f (union sets)) (union λ t → mapF f (sets t))
  exercise1'1iii1 {A = A} {T = T} f sets z = x ,, y
    where
      x : mapF f (union sets) z → union (λ t → mapF f (sets t)) z
      x (a , ((t , isIn) ,, snd)) = t , (a , (isIn ,, snd))
      y : union (λ t → mapF f (sets t)) z → mapF f (union sets) z
      y (t , (r , s)) = r , ((t , _&&_.fst s) ,, _&&_.snd s)

  exercise1'1iii2 : {a b c d : _} {A : Set a} {B : Set b} → (f : A → B) → equality B (mapF f (emptySet {b = c} A)) (emptySet {b = d} B)
  exercise1'1iii2 {A = A} {B = B} f z = x ,, λ ()
    where
      x : mapF f (emptySet A) z → emptySet B z
      x (a , ())

  ex4F : !1234 → !1234
  ex4F !1 = !1
  ex4F !2 = !2
  ex4F !3 = !1
  ex4F !4 = !4

  v1 : PowerSet !1234
  v1 !1 = True
  v1 !2 = True
  v1 !3 = False
  v1 !4 = False
  v2 : PowerSet !1234
  v2 !1 = False
  v2 !2 = True
  v2 !3 = True
  v2 !4 = False

  v1AndV2 : Bool → !1234 → Set
  v1AndV2 BoolTrue = v1
  v1AndV2 BoolFalse = v2

  lhs : equality {c = lzero} !1234 (mapF ex4F (intersection v1AndV2)) (singleton decidable1234 !2)
  lhs !1 = ans ,, λ ()
    where
      ans : mapF ex4F (intersection v1AndV2) !1 → False'
      ans (!1 , (fst ,, refl)) with fst BoolFalse
      ans (!1 , (fst ,, refl)) | ()
      ans (!3 , (fst ,, refl)) with fst BoolTrue
      ans (!3 , (fst ,, refl)) | ()
  lhs !2 = (λ _ → record {}) ,, ans
    where
      u : intersection v1AndV2 !2
      u BoolTrue = record {}
      u BoolFalse = record {}
      ans : singleton decidable1234 !2 !2 → mapF ex4F (intersection v1AndV2) !2
      ans _ = !2 , (u ,, refl)
  lhs !3 = ans ,, λ ()
    where
      ans : mapF ex4F (intersection v1AndV2) !3 → False'
      ans (!3 , (fst ,, ()))
  lhs !4 = ans ,, λ ()
    where
      ans : mapF ex4F (intersection v1AndV2) !4 → False'
      ans (!4 , (fst ,, refl)) with fst BoolTrue
      ans (!4 , (fst ,, refl)) | ()

  fv1AndV2 : Bool → !1234 → Set
  fv1AndV2 BoolTrue = mapF ex4F v1
  fv1AndV2 BoolFalse = mapF ex4F v2

  rhs : equality {c = lzero} !1234 (intersection fv1AndV2) (fromExtension decidable1234 (!2 :: !1 :: []))
  rhs !1 = (λ _ → record {}) ,, λ _ → a
    where
      a : intersection fv1AndV2 !1
      a BoolTrue = !1 , (record {} ,, refl)
      a BoolFalse = !3 , (record {} ,, refl)
  rhs !2 = (λ _ → record {}) ,, λ _ → a
    where
      a : intersection fv1AndV2 !2
      a BoolTrue = !2 , (record {} ,, refl)
      a BoolFalse = !2 , (record {} ,, refl)
  rhs !3 = a ,, λ ()
    where
      a : intersection fv1AndV2 !3 → fromExtension decidable1234 (!2 :: !1 :: []) !4
      a pr with pr BoolTrue
      a pr | !1 , (fst ,, ())
      a pr | !2 , (fst ,, ())
      a pr | !3 , (fst ,, snd) = fst
      a pr | !4 , (fst ,, snd) = fst
  rhs !4 = a ,, λ ()
    where
      a : intersection fv1AndV2 !4 → fromExtension decidable1234 (!2 :: !1 :: []) !4
      a pr with pr BoolTrue
      a pr | !1 , (x ,, ())
      a pr | !2 , (x ,, ())
      a pr | !3 , (x ,, ())
      a pr | !4 , (x ,, _) = x

  exercise1'1iv1 : (equality !1234 (mapF ex4F (intersection v1AndV2)) (intersection fv1AndV2)) → False
  exercise1'1iv1 pr = ohno
    where
      bad : equality !1234 (fromExtension decidable1234 (!2 :: !1 :: [])) (singleton decidable1234 !2)
      bad = trans (symm rhs) (trans (symm pr) lhs)
      ohno : False
      ohno with bad !1
      ohno | fst ,, snd with fst record {}
      ... | ()

  exercise1'1iv2 : (equality !1234 (mapF ex4F (λ _ → True)) (λ _ → True)) → False
  exercise1'1iv2 pr with pr !3
  exercise1'1iv2 pr | fst ,, snd with snd _
  exercise1'1iv2 pr | fst ,, snd | !1 , ()
  exercise1'1iv2 pr | fst ,, snd | !2 , ()
  exercise1'1iv2 pr | fst ,, snd | !3 , ()
  exercise1'1iv2 pr | fst ,, snd | !4 , ()

  exercise1'1iv3 : equality !1234 (mapF ex4F (complement v1)) (complement v1) → False
  exercise1'1iv3 pr with pr !1
  exercise1'1iv3 pr | fst ,, snd with fst (!3 , ((λ i → i) ,, refl)) (record {})
  ... | ()
