{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Vectors
open import Semirings.Definition
open import Categories.Definition
open import Groups.Definition
open import Setoids.Setoids
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Examples
open import Groups.Homomorphisms.Lemmas
open import Functions

module Categories.Examples where

SET : {a : _} → Category {lsuc a} {a}
Category.objects (SET {a}) = Set a
Category.arrows (SET {a}) = λ a b → (a → b)
Category.id (SET {a}) = λ x → λ y → y
Category._∘_ (SET {a}) = λ f g → λ x → f (g x)
Category.rightId (SET {a}) = λ f → refl
Category.leftId (SET {a}) = λ f → refl
Category.compositionAssociative (SET {a}) = λ f g h → refl

GROUP : {a b : _} → Category {lsuc a ⊔ lsuc b} {a ⊔ b}
Category.objects (GROUP {a} {b}) = Sg (Set a) (λ A → Sg (A → A → A) (λ _+_ → Sg (Setoid {a} {b} A) (λ S → Group S _+_)))
Category.arrows (GROUP {a}) (A , (_+A_ , (S , G))) (B , (_+B_ , (T , H))) = Sg (A → B) (GroupHom G H)
Category.id (GROUP {a}) (A , (_+A_ , (S , G))) = (λ i → i) , identityHom G
Category._∘_ (GROUP {a}) {A , (_+A_ , (S , G))} {B , (_+B_ , (T , H))} {C , (_+C_ , (U , I))} (f , fHom) (g , gHom) = (f ∘ g) , groupHomsCompose gHom fHom
Category.rightId (GROUP {a}) {A , (_+A_ , (S , G))} {B , (_+B_ , (T , H))} (f , fHom) = {!!}
Category.leftId (GROUP {a}) {A , (_+A_ , (S , G))} {B , (_+B_ , (T , H))} (f , fHom) = {!!}
Category.compositionAssociative (GROUP {a}) = {!!}

DISCRETE : {a : _} (X : Set a) → Category {a} {a}
Category.objects (DISCRETE X) = X
Category.arrows (DISCRETE X) = λ a b → a ≡ b
Category.id (DISCRETE X) = λ x → refl
Category._∘_ (DISCRETE X) = λ y=z x=y → transitivity x=y y=z
Category.rightId (DISCRETE X) refl = refl
Category.leftId (DISCRETE X) refl = refl
Category.compositionAssociative (DISCRETE X) refl refl refl = refl
