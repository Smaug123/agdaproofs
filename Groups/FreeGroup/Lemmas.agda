{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Groups.FreeGroup.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Decidable.Sets
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Semirings.Definition
open import Functions
open import Groups.Isomorphisms.Definition
open import Groups.FreeGroup.Word
open import Groups.FreeGroup.Group
open import Groups.FreeGroup.UniversalProperty
open import Groups.Abelian.Definition
open import Groups.QuotientGroup.Definition

module Groups.FreeGroup.Lemmas {a : _} {A : Set a} (decA : DecidableSet A) where

freeGroupNonAbelian : AbelianGroup (freeGroup decA) → (a : A) → Sg (A → True) Bijection
freeGroupNonAbelian record { commutative = commutative } a = (λ _ → record {}) , b
  where
    b : Bijection (λ _ → record {})
    Bijection.inj b {x} {y} _ with decA x y
    ... | inl pr = pr
    ... | inr neq = exFalso (neq (ofLetterInjective (prependLetterInjective' decA t)))
      where
        t : prependLetter {decA = decA} (ofLetter x) (prependLetter (ofLetter y) empty (wordEmpty refl)) (wordEnding (succIsPositive 0) refl) ≡ prependLetter (ofLetter y) (prependLetter (ofLetter x) empty (wordEmpty refl)) (wordEnding (succIsPositive 0) refl)
        t = commutative {prependLetter (ofLetter x) empty (wordEmpty refl)} {prependLetter (ofLetter y) empty (wordEmpty refl)}
    Bijection.surj b record {} = a , refl

freeGroupFunctorWellDefined : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → Bijection f → GroupsIsomorphic (freeGroup decA) (freeGroup decB)
GroupsIsomorphic.isomorphism (freeGroupFunctorWellDefined decB {f} bij) = universalPropertyFunction decA (freeGroup decB) λ a → freeEmbedding decB (f a)
GroupIso.groupHom (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)) = universalPropertyHom decA (freeGroup decB) λ a → freeEmbedding decB (f a)
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) refl = refl
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {empty} {empty} _ = refl
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {empty} {prependLetter letter u x} r = {!!}
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {prependLetter letter t x} {empty} = {!!}
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {prependLetter l t x} {prependLetter l2 u y} pr = {!!}
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) refl = refl
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) = {!!}

freeGroupFunctorInjective : {b : _} {B : Set b} (decB : DecidableSet B) → GroupsIsomorphic (freeGroup decA) (freeGroup decB) → Sg (A → B) (λ f → Bijection f)
freeGroupFunctorInjective decB iso = {!!}

everyGroupQuotientOfFreeGroup : {b : _} → (S : Setoid {a} {b} A) → {_+_ : A → A → A} → (G : Group S _+_) → GroupsIsomorphic G (quotientGroupByHom (freeGroup decA) (universalPropertyHom decA {!!} {!!}))
everyGroupQuotientOfFreeGroup = {!!}

everyFGGroupQuotientOfFGFreeGroup : {!!}
everyFGGroupQuotientOfFGFreeGroup = {!!}

freeGroupTorsionFree : {!!}
freeGroupTorsionFree = {!!}

freeGroupInfinite : {!!}
freeGroupInfinite = {!!}
