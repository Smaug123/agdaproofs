{-# OPTIONS --safe --warning=error #-}

open import Numbers.Naturals.Semiring
open import Groups.FreeProduct.Definition
open import Groups.FreeProduct.Setoid
open import Groups.FreeProduct.Group
open import Groups.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Isomorphisms.Definition
open import LogicalFormulae
open import Numbers.Integers.Addition
open import Numbers.Integers.Definition
open import Groups.FreeGroup.Definition
open import Groups.FreeGroup.Word
open import Groups.FreeGroup.Group
open import Groups.FreeGroup.UniversalProperty
open import Setoids.Setoids

module Groups.FreeProduct.Lemmas {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) where

private
  f : ReducedWord decidableIndex → ReducedSequence decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)
  f = universalPropertyFunction decidableIndex (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) λ i → nonempty i (ofEmpty i (nonneg 1) λ ())

  freeProductIso : GroupHom (freeGroup decidableIndex) (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) f
  freeProductIso = universalPropertyHom decidableIndex (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) (λ i → nonempty i (ofEmpty i (nonneg 1) λ ()))

  freeProductInj : (x y : ReducedWord decidableIndex) → (decidableIndex =RP λ _ → ℤDecideEquality) (λ _ → ℤGroup) (f x) (f y) → x ≡ y
  freeProductInj empty empty pr = refl
  freeProductInj empty (prependLetter (ofLetter x₁) y x) pr = exFalso {!!}
  freeProductInj empty (prependLetter (ofInv x₁) y x) pr = {!!}
  freeProductInj (prependLetter letter x x₁) y pr = {!!}

freeProductZ : GroupsIsomorphic (freeGroup decidableIndex) (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup))
GroupsIsomorphic.isomorphism (freeProductZ) = universalPropertyFunction decidableIndex (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) λ i → nonempty i (ofEmpty i (nonneg 1) λ ())
GroupIso.groupHom (GroupsIsomorphic.proof (freeProductZ)) = freeProductIso
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) = GroupHom.wellDefined (freeProductIso)
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) {x} {y} = freeProductInj x y
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) = GroupHom.wellDefined freeProductIso
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) {empty} = empty , record {}
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) {nonempty i (ofEmpty .i (nonneg zero) nonZero)} = exFalso (nonZero refl)
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) {nonempty i (ofEmpty .i (nonneg (succ x)) nonZero)} = prependLetter (ofLetter i) empty (wordEmpty refl) , {!!}
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) {nonempty i (ofEmpty .i (negSucc x) nonZero)} = {!!}
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ)))) {nonempty i (prependLetter .i g nonZero x x₁)} = {!!}

freeProductNonAbelian : {!!}
freeProductNonAbelian = {!!}
