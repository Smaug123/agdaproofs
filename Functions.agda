{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae

module Functions where
  Rel : {a b : _} → Set a → Set (a ⊔ lsuc b)
  Rel {a} {b} A = A → A → Set b

  _∘_ : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → (f : B → C) → (g : A → B) → (A → C)
  g ∘ f = λ a → g (f a)

  record Injection {a b : _} {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
    field
      property : {x y : A} → (f x ≡ f y) → x ≡ y

  record Surjection {a b : _} {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
    field
      property : (b : B) → Sg A (λ a → f a ≡ b)

  record Bijection {a b : _} {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
    field
      inj : Injection f
      surj : Surjection f

  record Invertible {a b : _} {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
    field
      inverse : B → A
      isLeft : (b : B) → f (inverse b) ≡ b
      isRight : (a : A) → inverse (f a) ≡ a

  invertibleImpliesBijection : {a b : _} {A : Set a} {B : Set b} {f : A → B} → Invertible f → Bijection f
  Injection.property (Bijection.inj (invertibleImpliesBijection {a} {b} {A} {B} {f} record { inverse = inverse ; isLeft = isLeft ; isRight = isRight })) {x} {y} fx=fy = ans
    where
      bl : inverse (f x) ≡ inverse (f y)
      bl = applyEquality inverse fx=fy
      ans : x ≡ y
      ans rewrite equalityCommutative (isRight x) | equalityCommutative (isRight y) = bl
  Surjection.property (Bijection.surj (invertibleImpliesBijection {a} {b} {A} {B} {f} record { inverse = inverse ; isLeft = isLeft ; isRight = isRight })) y = (inverse y , isLeft y)

  bijectionImpliesInvertible : {a b : _} {A : Set a} {B : Set b} {f : A → B} → Bijection f → Invertible f
  Invertible.inverse (bijectionImpliesInvertible record { inj = inj ; surj = record { property = property } }) b = underlying (property b)
  Invertible.isLeft (bijectionImpliesInvertible {f = f} record { inj = inj ; surj = surj }) b with Surjection.property surj b
  Invertible.isLeft (bijectionImpliesInvertible {f = f} record { inj = inj ; surj = surj }) b | a , prop = prop
  Invertible.isRight (bijectionImpliesInvertible {f = f} record { inj = inj ; surj = surj }) a with Surjection.property surj (f a)
  Invertible.isRight (bijectionImpliesInvertible {f = f} record { inj = record { property = property } ; surj = surj }) a | a₁ , b = property b

  injComp : {a b c : _} {A : Set a} {B : Set b} {C : Set c} {f : A → B} {g : B → C} → Injection f → Injection g → Injection (g ∘ f)
  Injection.property (injComp {f = f} {g} record { property = propF } record { property = propG }) pr = propF (propG pr)

  surjComp : {a b c : _} {A : Set a} {B : Set b} {C : Set c} {f : A → B} {g : B → C} → Surjection f → Surjection g → Surjection (g ∘ f)
  Surjection.property (surjComp {f = f} {g} record { property = propF } record { property = propG }) c with propG c
  Surjection.property (surjComp {f = f} {g} record { property = propF } record { property = propG }) c | b , pr with propF b
  Surjection.property (surjComp {f = f} {g} record { property = propF } record { property = propG }) c | b , pr | a , pr2 = a , pr'
    where
      pr' : g (f a) ≡ c
      pr' rewrite pr2 = pr

  bijectionComp : {a b c : _} {A : Set a} {B : Set b} {C : Set c} {f : A → B} {g : B → C} → Bijection f → Bijection g → Bijection (g ∘ f)
  Bijection.inj (bijectionComp bijF bijG) = injComp (Bijection.inj bijF) (Bijection.inj bijG)
  Bijection.surj (bijectionComp bijF bijG) = surjComp (Bijection.surj bijF) (Bijection.surj bijG)

  compInjRightInj : {a b c : _} {A : Set a} {B : Set b} {C : Set c} {f : A → B} {g : B → C} → Injection (g ∘ f) → Injection f
  Injection.property (compInjRightInj {f = f} {g} record { property = property }) {x} {y} fx=fy = property (applyEquality g fx=fy)

  compSurjLeftSurj : {a b c : _} {A : Set a} {B : Set b} {C : Set c} {f : A → B} {g : B → C} → Surjection (g ∘ f) → Surjection g
  Surjection.property (compSurjLeftSurj {f = f} {g} record { property = property }) b with property b
  Surjection.property (compSurjLeftSurj {f = f} {g} record { property = property }) b | a , b1 = f a , b1

  injectionPreservedUnderExtensionalEq : {a b : _} {A : Set a} {B : Set b} {f g : A → B} → Injection f → ({x : A} → f x ≡ g x) → Injection g
  Injection.property (injectionPreservedUnderExtensionalEq {A = A} {B} {f} {g} record { property = property } prop) {x} {y} gx=gy = property (transitivity (prop {x}) (transitivity gx=gy (equalityCommutative (prop {y}))))

  surjectionPreservedUnderExtensionalEq : {a b : _} {A : Set a} {B : Set b} {f g : A → B} → Surjection f → ({x : A} → f x ≡ g x) → Surjection g
  Surjection.property (surjectionPreservedUnderExtensionalEq {f = f} {g} surj ext) b with (Surjection.property surj b)
  Surjection.property (surjectionPreservedUnderExtensionalEq {f = f} {g} surj ext) b | a , pr = a , transitivity (equalityCommutative ext) pr

  bijectionPreservedUnderExtensionalEq : {a b : _} {A : Set a} {B : Set b} {f g : A → B} → Bijection f → ({x : A} → f x ≡ g x) → Bijection g
  Bijection.inj (bijectionPreservedUnderExtensionalEq record { inj = inj ; surj = surj } ext) = injectionPreservedUnderExtensionalEq inj ext
  Bijection.surj (bijectionPreservedUnderExtensionalEq record { inj = inj ; surj = surj } ext) = surjectionPreservedUnderExtensionalEq surj ext

  inverseIsInvertible : {a b : _} {A : Set a} {B : Set b} {f : A → B} → (inv : Invertible f) → Invertible (Invertible.inverse inv)
  Invertible.inverse (inverseIsInvertible {f = f} inv) = f
  Invertible.isLeft (inverseIsInvertible {f = f} inv) b = Invertible.isRight inv b
  Invertible.isRight (inverseIsInvertible {f = f} inv) a = Invertible.isLeft inv a

  id : {a : _} {A : Set a} → (A → A)
  id a = a

  idIsBijective : {a : _} {A : Set a} → Bijection (id {a} {A})
  Injection.property (Bijection.inj idIsBijective) pr = pr
  Surjection.property (Bijection.surj idIsBijective) b = b , refl

  functionCompositionExtensionallyAssociative : {a b c d : _} {A : Set a} {B : Set b} {C : Set c} {D : Set d} → (f : A → B) → (g : B → C) → (h : C → D) → (x : A) → (h ∘ (g ∘ f)) x ≡ ((h ∘ g) ∘ f) x
  functionCompositionExtensionallyAssociative f g h x = refl

  dom : {a b : _} {A : Set a} {B : Set b} (f : A → B) → Set a
  dom {A = A} f = A

  codom : {a b : _} {A : Set a} {B : Set b} (f : A → B) → Set b
  codom {B = B} f = B
