{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module LogicalFormulae where

infix 5 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

data False : Set where
data False' {a : _} : Set a where

record True : Set where
{-# BUILTIN UNIT True #-}
record True' {a : _} : Set a where

infix 10 _||_
data _||_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A || B
  inr : B → A || B

infix 15 _&&_
record _&&_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,,_
  field
    fst : A
    snd : B

equalityLeft : {a b : _} {A : Set a} {B : Set b} {x1 x2 : A && B} → (x1 ≡ x2) → _&&_.fst x1 ≡ _&&_.fst x2
equalityLeft {x1 = a ,, _} {.a ,, _} refl = refl

equalityRight : {a b : _} {A : Set a} {B : Set b} {x1 x2 : A && B} → (x1 ≡ x2) → _&&_.snd x1 ≡ _&&_.snd x2
equalityRight {x1 = _ ,, a} {_ ,, .a} refl = refl

infix 15 _&_&_
record _&_&_ {a b c} (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where
  field
    one : A
    two : B
    three : C

data Sg {n : _} {m : _} (A : Set m) (B : A → Set n) : Set (m ⊔ n) where
  _,_ : (a : A) → (b : B a) → Sg A B

underlying : {n m : _} {A : _} {prop : _} → Sg {n} {m} A prop -> A
underlying (a , b) = a

underlyingRefl : {n m : _} {A : _} {prop : _} → {r s : Sg {n} {m} A prop} → r ≡ s → underlying r ≡ underlying s
underlyingRefl {r = (a , b)} {(.a , .b)} refl = refl

transitivity : {a : _} {A : Set a} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
transitivity refl refl = refl

liftEquality : {a : _} {A B : Set a} (f g : A → B) → (x y : A) → (f ≡ g) → (x ≡ y) → ((f x) ≡ (g y))
liftEquality f .f x .x refl refl = refl

applyEquality : {a : _} {b : _} {A : Set a} {B : Set b} (f : A → B) → {x y : A} → (x ≡ y) → ((f x) ≡ (f y))
applyEquality {A} {B} f {x} {.x} refl = refl

applyEquality2 : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) → {x y : A} → (x ≡ y) → {m n : B} → (m ≡ n) → f x m ≡ f y n
applyEquality2 f x=y m=n rewrite x=y | m=n = refl

identityOfIndiscernablesLeft : {m n o : _} {A : Set m} {B : Set n} {a : A} {b : B} {c : A} → (prop : A → B → Set o) → (prop a b) → (a ≡ c) → (prop c b)
identityOfIndiscernablesLeft {a = a} {b} {.a} prop pAB refl = pAB

identityOfIndiscernablesRight : {m n o : _} {A : Set m} {B : Set n} {a : A} {b c : B} → (prop : A → B → Set o) → (prop a b) → (b ≡ c) → (prop a c)
identityOfIndiscernablesRight {a = a} {b} {.b} prop prAB refl = prAB

equalityCommutative : {a : _} {A : Set a} {x y : A} → (x ≡ y) → (y ≡ x)
equalityCommutative refl = refl

exFalso : {n : _} {A : Set n} → .(x : False) → A
exFalso {a} = λ ()

exFalso' : {r n : _} {A : Set n} → .(x : False' {r}) → A
exFalso' ()

orIsAssociative : {n : _} {a b c : Set n} → ((a || b) || c) → (a || (b || c))
orIsAssociative (inl (inl x)) = inl x
orIsAssociative (inl (inr x)) = inr (inl x)
orIsAssociative (inr x) = inr (inr x)

lemConstructive : {n : _} → {p : Set n} → (p || (p → False)) → (((p → False) → False) → p)
lemConstructive (inl p) = λ _ → p
lemConstructive (inr notP) = λ negnegP → exFalso (negnegP notP)

lemConverse : {n : _} → {p : Set n} → p → ((p → False) → False)
lemConverse p = λ notP → notP p

typeCast : {a : _} {A : Set a} {B : Set a} (el : A) (pr : A ≡ B) → B
typeCast {a} {A} {.A} elt refl = elt

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

curry : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) → ((Sg A (λ _ → B)) → C)
curry f (a , b) = f a b

uncurry : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (f : (Sg A (λ _ → B)) → C) → (A → B → C)
uncurry f a b = f (a , b)

decidableOr : {a b : _} → (A : Set a) → (B : Set b) → (A || (A → False)) → (A || B) → (A || ((A → False) && B))
decidableOr {a} {b} A B decidable (inl x) = inl x
decidableOr {a} {b} A B (inl y) (inr x) = inl y
decidableOr {a} {b} A B (inr y) (inr x) = inr (record { fst = y ; snd = x})

embedLevel : {a b : _} → Set a → Set (a ⊔ b)
embedLevel {a} {b} A = A && (True' {b})
