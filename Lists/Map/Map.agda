{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions.Definition
open import Lists.Definition
open import Lists.Fold.Fold
open import Lists.Length

module Lists.Map.Map where

map : {a b : _} {A : Set a} {B : Set b} (f : A → B) → List A → List B
map f [] = []
map f (x :: list) = (f x) :: (map f list)

map' : {a b : _} {A : Set a} {B : Set b} (f : A → B) → List A → List B
map' f = fold (λ a → (f a) ::_ ) []

map=map' : {a b : _} {A : Set a} {B : Set b} (f : A → B) → (l : List A) → (map f l ≡ map' f l)
map=map' f [] = refl
map=map' f (x :: l) with map=map' f l
... | bl = applyEquality (f x ::_) bl

mapId : {a : _} {A : Set a} (l : List A) → map id l ≡ l
mapId [] = refl
mapId (x :: l) rewrite mapId l = refl

mapMap : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → (l : List A) → {f : A → B} {g : B → C} → map g (map f l) ≡ map (g ∘ f) l
mapMap [] = refl
mapMap (x :: l) {f = f} {g} rewrite mapMap l {f} {g} = refl

mapExtension : {a b : _} {A : Set a} {B : Set b} (l : List A) (f g : A → B) → ({x : A} → (f x ≡ g x)) → map f l ≡ map g l
mapExtension [] f g pr = refl
mapExtension (x :: l) f g pr rewrite mapExtension l f g pr | pr {x} = refl

mapConcat : {a b : _} {A : Set a} {B : Set b} (l1 l2 : List A) (f : A → B) → map f (l1 ++ l2) ≡ (map f l1) ++ (map f l2)
mapConcat [] l2 f = refl
mapConcat (x :: l1) l2 f rewrite mapConcat l1 l2 f = refl

lengthMap : {a b : _} {A : Set a} {B : Set b} → (l : List A) → {f : A → B} → length l ≡ length (map f l)
lengthMap [] {f} = refl
lengthMap (x :: l) {f} rewrite lengthMap l {f} = refl
