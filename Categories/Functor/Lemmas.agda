{-# OPTIONS --warning=error --without-K --safe #-}

open import LogicalFormulae
open import Categories.Definition
open import Categories.Functor.Definition

module Categories.Functor.Lemmas where

functorCompose : {a b c d e f : _} {B : Category {a} {b}} {C : Category {c} {d}} {D : Category {e} {f}} → (Functor C D) → (Functor B C) → (Functor B D)
functorCompose G F = record { onObj = λ x → Functor.onObj G (Functor.onObj F x) ; onArrow = λ f → Functor.onArrow G (Functor.onArrow F f) ; mapId = λ {T} → mapIdHelp G F T ; mapCompose = λ r s → mapComposeHelp G F r s }
  where
    mapIdHelp : {a b c d e f : _} {B : Category {a} {b}} {C : Category {c} {d}} {D : Category {e} {f}} → (G : Functor C D) → (F : Functor B C) → (T : Category.objects B) → Functor.onArrow G (Functor.onArrow F (Category.id B T)) ≡ Category.id D (Functor.onObj G (Functor.onObj F T))
    mapIdHelp {B = B} {C} {D} record { onObj = onObjG ; onArrow = onArrowG ; mapId = mapIdG ; mapCompose = mapComposeG } record { onObj = onObj ; onArrow = onArrow ; mapId = mapId ; mapCompose = mapCompose } T rewrite mapId {T} = mapIdG {onObj T}
    mapComposeHelp : {a b c d e f : _} {B : Category {a} {b}} {C : Category {c} {d}} {D : Category {e} {f}} → (G : Functor C D) → (F : Functor B C) → {S T U : Category.objects B} → (r : Category.arrows B S T) → (s : Category.arrows B T U) → (Functor.onArrow G (Functor.onArrow F (Category._∘_ B s r))) ≡ (Category._∘_ D (Functor.onArrow G (Functor.onArrow F s)) (Functor.onArrow G (Functor.onArrow F r)))
    mapComposeHelp {B = record { objects = objectsB ; arrows = arrowsB ; id = idB ; _∘_ = _∘B_ ; rightId = rightIdB ; leftId = leftIdB ; compositionAssociative = associativeB }} {record { objects = objectsC ; arrows = arrowsC ; id = idC ; _∘_ = _∘C_ ; rightId = rightIdC ; leftId = leftIdC ; compositionAssociative = associativeC }} {record { objects = objectsD ; arrows = arrowsD ; id = idD ; _∘_ = _∘D_ ; rightId = rightIdD ; leftId = leftIdD ; compositionAssociative = associativeD }} record { onObj = onObjG ; onArrow = onArrowG ; mapId = mapIdG ; mapCompose = mapComposeG } record { onObj = onObjF ; onArrow = onArrowF ; mapId = mapIdF ; mapCompose = mapComposeF } {S} {T} {U} r s rewrite mapComposeF r s | mapComposeG (onArrowF r) (onArrowF s) = refl

idFunctor : {a b : _} (C : Category {a} {b}) → Functor C C
Functor.onObj (idFunctor C) = λ x → x
Functor.onArrow (idFunctor C) = λ f → f
Functor.mapId (idFunctor C) = refl
Functor.mapCompose (idFunctor C) = λ f g → refl
