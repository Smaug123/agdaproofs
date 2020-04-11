{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Decidable.Sets

module Decidable.Lemmas {a : _} {A : Set a} (dec : DecidableSet A) where

squash : {x y : A} → .(x ≡ y) → x ≡ y
squash {x} {y} x=y with dec x y
... | inl pr = pr
... | inr bad = exFalso (bad x=y)
