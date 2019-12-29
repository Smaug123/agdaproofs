{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Semirings.Definition
open import Sets.CantorBijection.Proofs

module Sets.CantorBijection.CantorBijection where

  open Sets.CantorBijection.Proofs using (cantorInverse ; cantorInverseLemma) public

  cantorBijection : Bijection cantorInverse
  Injection.property (Bijection.inj cantorBijection) {x} {y} = cantorInverseInjective x y
  Surjection.property (Bijection.surj cantorBijection) = cantorInverseSurjective
