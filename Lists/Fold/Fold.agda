{-# OPTIONS --safe --warning=error --without-K #-}

open import Lists.Definition

module Lists.Fold.Fold {a b : _} {A : Set a} {B : Set b} where

fold : (f : A → B → B) → B → List A → B
fold f default [] = default
fold f default (x :: l) = f x (fold f default l)
