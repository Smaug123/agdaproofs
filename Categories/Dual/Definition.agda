{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Categories.Definition

module Categories.Dual.Definition where

dual : {a b : _} → Category {a} {b} → Category {a} {b}
dual record { objects = objects ; arrows = arrows ; id = id ; _∘_ = _∘_ ; rightId = rightId ; leftId = leftId ; compositionAssociative = associative } = record { objects = objects ; arrows = λ i j → arrows j i ; id = id ; _∘_ = λ {x y z} g f → f ∘ g ; rightId = λ {x y} f → leftId f ; leftId = λ {x y} f → rightId f ; compositionAssociative = λ {x y z w} f g h → equalityCommutative (associative h g f) }
