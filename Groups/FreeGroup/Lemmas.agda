{-# OPTIONS --safe --warning=error #-}

open import Sets.Cardinality.Infinite.Definition
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
open import Groups.Lemmas

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

mapIntoFreeGroupInjective : {b c : _} {B : Set b} {S : Setoid {b} {c} B} {_+_ : B → B → B} (G : Group S _+_) → {f : A → B} → SetoidInjection (reflSetoid A) S f → SetoidInjection (reflSetoid (ReducedWord decA)) S (universalPropertyFunction decA G (λ a → f a))
SetoidInjection.wellDefined (mapIntoFreeGroupInjective {S = S} G {f} inj) {x} {.x} refl = Equivalence.reflexive (Setoid.eq S)
SetoidInjection.injective (mapIntoFreeGroupInjective G {f} inj) {empty} {empty} pr = refl
SetoidInjection.injective (mapIntoFreeGroupInjective {S = S} G {f} inj) {empty} {prependLetter (ofLetter l) y x} pr with SetoidInjection.injective inj {l} {{!!}} (Equivalence.transitive (Setoid.eq S) (transferToRight' G (Equivalence.symmetric (Setoid.eq S) pr)) {!!})
... | bl = {!!}
SetoidInjection.injective (mapIntoFreeGroupInjective G {f} inj) {empty} {prependLetter (ofInv l) y x} pr = {!!}
SetoidInjection.injective (mapIntoFreeGroupInjective G {f} inj) {prependLetter letter x x₁} {y} pr = {!!}

freeGroupFunctorWellDefined : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → Bijection f → GroupsIsomorphic (freeGroup decA) (freeGroup decB)
GroupsIsomorphic.isomorphism (freeGroupFunctorWellDefined decB {f} bij) = universalPropertyFunction decA (freeGroup decB) λ a → freeEmbedding decB (f a)
GroupIso.groupHom (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)) = universalPropertyHom decA (freeGroup decB) λ a → freeEmbedding decB (f a)
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) refl = refl
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {empty} {empty} _ = refl
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {empty} {prependLetter letter u x} r = {!!}
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {prependLetter letter t x} {empty} = {!!}
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {prependLetter l t x} {prependLetter l2 u y} pr = {!!}
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) refl = refl
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {x} = {!!}

freeGroupFunctorInjective : {b : _} {B : Set b} (decB : DecidableSet B) → GroupsIsomorphic (freeGroup decA) (freeGroup decB) → Sg (A → B) (λ f → Bijection f)
freeGroupFunctorInjective decB iso = {!!}

everyGroupQuotientOfFreeGroup : {b : _} → (S : Setoid {a} {b} A) → {_+_ : A → A → A} → (G : Group S _+_) → GroupsIsomorphic G (quotientGroupByHom (freeGroup decA) (universalPropertyHom decA {!!} {!!}))
everyGroupQuotientOfFreeGroup = {!!}

everyFGGroupQuotientOfFGFreeGroup : {!!}
everyFGGroupQuotientOfFGFreeGroup = {!!}

freeGroupTorsionFree : {!!}
freeGroupTorsionFree = {!!}

private
  mapNToGrp : (a : A) → (n : ℕ) → ReducedWord decA
  mapNToGrpLen : (a : A) → (n : ℕ) → wordLength decA (mapNToGrp a n) ≡ n
  mapNToGrpFirstLetter : (a : A) → (n : ℕ) → .(pr : 0 <N wordLength decA (mapNToGrp a (succ n))) → firstLetter decA (mapNToGrp a (succ n)) pr ≡ (ofLetter a)
  lemma : (a : A) → (n : ℕ) → .(pr : 0 <N wordLength decA (mapNToGrp a (succ n))) → ofLetter a ≡ freeInverse (firstLetter decA (mapNToGrp a (succ n)) pr) → False

  lemma a zero _ ()
  lemma a (succ n) _ ()

  mapNToGrp a zero = empty
  mapNToGrp a 1 = prependLetter (ofLetter a) empty (wordEmpty refl)
  mapNToGrp a (succ (succ n)) = prependLetter (ofLetter a) (mapNToGrp a (succ n)) (wordEnding (identityOfIndiscernablesRight _<N_ (succIsPositive n) (equalityCommutative (mapNToGrpLen a (succ n)))) (freeCompletionEqualFalse decA λ p → lemma a n ((identityOfIndiscernablesRight _<N_ (succIsPositive n) (equalityCommutative (mapNToGrpLen a (succ n))))) p))

  mapNToGrpFirstLetter a zero pr = refl
  mapNToGrpFirstLetter a (succ n) pr = refl

  mapNToGrpLen a zero = refl
  mapNToGrpLen a (succ zero) = refl
  mapNToGrpLen a (succ (succ n)) = applyEquality succ (mapNToGrpLen a (succ n))

  mapNToGrpInj : (a : A) → (x y : ℕ) → mapNToGrp a x ≡ mapNToGrp a y → x ≡ y
  mapNToGrpInj a zero zero pr = refl
  mapNToGrpInj a zero (succ zero) ()
  mapNToGrpInj a zero (succ (succ y)) ()
  mapNToGrpInj a (succ zero) zero ()
  mapNToGrpInj a (succ (succ x)) zero ()
  mapNToGrpInj a (succ zero) (succ zero) pr = refl
  mapNToGrpInj a (succ (succ x)) (succ (succ y)) pr = applyEquality succ (mapNToGrpInj a (succ x) (succ y) (prependLetterInjective decA pr))

freeGroupInfinite : (nonempty : A) → DedekindInfiniteSet (ReducedWord decA)
DedekindInfiniteSet.inj (freeGroupInfinite nonempty) = mapNToGrp nonempty
DedekindInfiniteSet.isInjection (freeGroupInfinite nonempty) {x} {y} = mapNToGrpInj nonempty x y
