{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions.Definition
open import Sets.CantorBijection.Proofs

module Sets.CantorBijection.CantorBijection where

open Sets.CantorBijection.Proofs using (cantorInverse ; cantorInverseLemma) public

cantorBijection : Bijection cantorInverse
Bijection.inj cantorBijection {x} {y} = cantorInverseInjective x y
Bijection.surj cantorBijection = cantorInverseSurjective
