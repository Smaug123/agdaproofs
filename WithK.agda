{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae

module WithK where

typeCastEqual : {a : _} {A : Set a} {B : Set a} {el : A} (pr1 pr2 : A ≡ B) → (typeCast el pr1) ≡ (typeCast el pr2)
typeCastEqual {a} {A} {.A} {el} refl refl = refl

reflRefl : {a : _} {A : Set a} → {r s : A} → (pr1 pr2 : r ≡ s) → pr1 ≡ pr2
reflRefl refl refl = refl
