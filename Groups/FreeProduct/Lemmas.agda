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

module Groups.FreeProduct.Lemmas where

private
  f : {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) → ReducedWord decidableIndex → ReducedSequence decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)
  f decidableIndex = universalPropertyFunction decidableIndex (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) λ i → nonempty i (ofEmpty i (nonneg 1) λ ())

  freeProductIso : {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) → GroupHom (freeGroup decidableIndex) (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) (f decidableIndex)
  freeProductIso decidableIndex = universalPropertyHom decidableIndex (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) (λ i → nonempty i (ofEmpty i (nonneg 1) λ ()))

  freeProductInj : {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) → (x y : ReducedWord decidableIndex) → (decidableIndex =RP λ _ → ℤDecideEquality) (λ _ → ℤGroup) (f decidableIndex x) (f decidableIndex y) → x ≡ y
  freeProductInj decidableIndex empty empty pr = refl
  freeProductInj decidableIndex empty (prependLetter (ofLetter x₁) y x) pr = exFalso {!!}
  freeProductInj decidableIndex empty (prependLetter (ofInv x₁) y x) pr = {!!}
  freeProductInj decidableIndex (prependLetter letter x x₁) y pr = {!!}

freeProductZ : {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) → GroupsIsomorphic (freeGroup decidableIndex) (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup))
GroupsIsomorphic.isomorphism (freeProductZ decidableIndex) = universalPropertyFunction decidableIndex (FreeProductGroup decidableIndex (λ _ → ℤDecideEquality) (λ _ → ℤGroup)) λ i → nonempty i (ofEmpty i (nonneg 1) λ ())
GroupIso.groupHom (GroupsIsomorphic.proof (freeProductZ decidableIndex)) = freeProductIso decidableIndex
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) = GroupHom.wellDefined (freeProductIso decidableIndex)
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) {x} {y} = freeProductInj decidableIndex x y
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) = GroupHom.wellDefined (freeProductIso decidableIndex)
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) {empty} = empty , record {}
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) {nonempty i (ofEmpty .i (nonneg zero) nonZero)} = exFalso (nonZero refl)
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) {nonempty i (ofEmpty .i (nonneg (succ x)) nonZero)} = prependLetter (ofLetter i) empty (wordEmpty refl) , {!!}
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) {nonempty i (ofEmpty .i (negSucc x) nonZero)} = {!!}
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeProductZ decidableIndex)))) {nonempty i (prependLetter .i g nonZero x x₁)} = {!!}

freeProductNonAbelian : {!!}
freeProductNonAbelian = {!!}

freeProductInfinite : {!!}
freeProductInfinite = {!!}
