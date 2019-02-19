{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module DecidableSet where

  record DecidableSet {a : _} (A : Set a) : Set a where
    field
      eq : (a b : A) → ((a ≡ b) || ((a ≡ b) → False))
