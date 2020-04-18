{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae

module Functions.Definition where

Rel : {a b : _} → Set a → Set (a ⊔ lsuc b)
Rel {a} {b} A = A → A → Set b

_∘_ : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → (f : B → C) → (g : A → B) → (A → C)
g ∘ f = λ a → g (f a)

Injection : {a b : _} {A : Set a} {B : Set b} (f : A → B) → Set (a ⊔ b)
Injection {A = A} f = {x y : A} → (f x ≡ f y) → x ≡ y

Surjection : {a b : _} {A : Set a} {B : Set b} (f : A → B) → Set (a ⊔ b)
Surjection {A = A} {B = B} f = (b : B) → Sg A (λ a → f a ≡ b)

record Bijection {a b : _} {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
  field
    inj : Injection f
    surj : Surjection f

record Invertible {a b : _} {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
  field
    inverse : B → A
    isLeft : (b : B) → f (inverse b) ≡ b
    isRight : (a : A) → inverse (f a) ≡ a

id : {a : _} {A : Set a} → (A → A)
id a = a

dom : {a b : _} {A : Set a} {B : Set b} (f : A → B) → Set a
dom {A = A} f = A

codom : {a b : _} {A : Set a} {B : Set b} (f : A → B) → Set b
codom {B = B} f = B
