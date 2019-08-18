{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Maybe where
  data Maybe {a : _} (A : Set a) : Set a where
    no : Maybe A
    yes : A → Maybe A

  joinMaybe : {a : _} → {A : Set a} → Maybe (Maybe A) → Maybe A
  joinMaybe no = no
  joinMaybe (yes s) = s

  bindMaybe : {a b : _} → {A : Set a} → {B : Set b} → Maybe A → (A → Maybe B) → Maybe B
  bindMaybe no f = no
  bindMaybe (yes x) f = f x

  applyMaybe : {a b : _} → {A : Set a} → {B : Set b} → Maybe (A → B) → Maybe A → Maybe B
  applyMaybe f no = no
  applyMaybe no (yes x) = no
  applyMaybe (yes f) (yes x) = yes (f x)

  yesInjective : {a : _} → {A : Set a} → {x y : A} → (yes x ≡ yes y) → x ≡ y
  yesInjective {a} {A} {x} {.x} refl = refl

  mapMaybe : {a b : _} → {A : Set a} → {B : Set b} → (f : A → B) → Maybe A → Maybe B
  mapMaybe f no = no
  mapMaybe f (yes x) = yes (f x)

  defaultValue : {a : _} → {A : Set a} → (default : A) → Maybe A → A
  defaultValue default no = default
  defaultValue default (yes x) = x
