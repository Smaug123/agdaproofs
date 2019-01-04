{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae

module LogicalFormulaeProofs where
  transitivity : LogicalFormulae.transitivity
  transitivity refl refl = refl
