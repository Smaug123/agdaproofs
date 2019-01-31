{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals -- for length

module Lists where
  data List {a} (A : Set a) : Set a where
    [] : List A
    _::_ : (x : A) (l : List A) → List A
