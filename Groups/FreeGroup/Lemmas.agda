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
open import Functions.Definition
open import Functions.Lemmas
open import Groups.Isomorphisms.Definition
open import Groups.FreeGroup.Word
open import Groups.FreeGroup.Group
open import Groups.FreeGroup.UniversalProperty
open import Groups.Abelian.Definition
open import Groups.QuotientGroup.Definition
open import Groups.Lemmas
open import Groups.Homomorphisms.Lemmas

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

private
  iso : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → Bijection f → ReducedWord decA → ReducedWord decB
  iso decB {f} bij = universalPropertyFunction decA (freeGroup decB) λ a → freeEmbedding decB (f a)

  isoHom : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → GroupHom (freeGroup decA) (freeGroup decB) (iso decB bij)
  isoHom decB {f} bij = universalPropertyHom decA (freeGroup decB) λ a → iso decB bij (freeEmbedding decA a)

  iso2 : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → Bijection f → ReducedWord decB → ReducedWord decA
  iso2 decB {f} bij = universalPropertyFunction decB (freeGroup decA) λ b → freeEmbedding decA (Invertible.inverse (bijectionImpliesInvertible bij) b)

  iso2Hom : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → GroupHom (freeGroup decB) (freeGroup decA) (iso2 decB bij)
  iso2Hom decB {f} bij = universalPropertyHom decB (freeGroup decA) λ b → iso2 decB bij (freeEmbedding decB b)

  fixesF : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : A) → iso2 decB bij (iso decB bij (freeEmbedding decA x)) ≡ freeEmbedding decA x
  fixesF decB {f} bij x with Bijection.surj bij (f x)
  ... | _ , pr rewrite Bijection.inj bij pr = refl

  fixesF' : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : B) → iso decB bij (iso2 decB bij (freeEmbedding decB x)) ≡ freeEmbedding decB x
  fixesF' decB {f} bij x with Bijection.surj bij x
  ... | _ , pr rewrite pr = refl

  uniq : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : ReducedWord decA) → x ≡ universalPropertyFunction decA (freeGroup decA) (λ x → iso2 decB bij (iso decB bij (freeEmbedding decA x))) x
  uniq decB {f} bij x = universalPropertyUniqueness decA (freeGroup decA) (λ x → iso2 decB bij (iso decB bij (freeEmbedding decA x))) {id} (record { wellDefined = id ; groupHom = refl }) (fixesF decB bij) x
  uniqLemm : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : ReducedWord decA) → iso2 decB bij (iso decB bij x) ≡ universalPropertyFunction decA (freeGroup decA) (λ x → iso2 decB bij (iso decB bij (freeEmbedding decA x))) x
  uniqLemm decB {f} bij x = universalPropertyUniqueness decA (freeGroup decA) (λ i → freeEmbedding decA (underlying (Bijection.surj bij (f i)))) {λ i → iso2 decB bij (iso decB bij i)} (groupHomsCompose (isoHom decB bij) (iso2Hom decB bij)) (λ _ → refl) x
  uniq! : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : ReducedWord decA) → iso2 decB bij (iso decB bij x) ≡ x
  uniq! decB bij x = transitivity (uniqLemm decB bij x) (equalityCommutative (uniq decB bij x))

  uniq' : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : ReducedWord decB) → x ≡ universalPropertyFunction decB (freeGroup decB) (λ x → iso decB bij (iso2 decB bij (freeEmbedding decB x))) x
  uniq' decB {f} bij x = universalPropertyUniqueness decB (freeGroup decB) (λ x → iso decB bij (iso2 decB bij (freeEmbedding decB x))) {id} (record { wellDefined = id ; groupHom = refl }) (fixesF' decB bij) x
  uniq'Lemm : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : ReducedWord decB) → iso decB bij (iso2 decB bij x) ≡ universalPropertyFunction decB (freeGroup decB) (λ x → iso decB bij (iso2 decB bij (freeEmbedding decB x))) x
  uniq'Lemm decB {f} bij x = universalPropertyUniqueness decB (freeGroup decB) (λ i → freeEmbedding decB (f (Invertible.inverse (bijectionImpliesInvertible bij) i))) {λ i → iso decB bij (iso2 decB bij i)} (groupHomsCompose (iso2Hom decB bij) (isoHom decB bij)) (λ _ → refl) x
  uniq'! : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → (bij : Bijection f) → (x : ReducedWord decB) → iso decB bij (iso2 decB bij x) ≡ x
  uniq'! decB bij x = transitivity (uniq'Lemm decB bij x) (equalityCommutative (uniq' decB bij x))

  inBijection : {b : _} {B : Set b} (decB : DecidableSet B) {f : A → B} (bij : Bijection f) → Bijection (iso decB bij)
  inBijection decB bij = invertibleImpliesBijection (record { inverse = iso2 decB bij ; isLeft = uniq'! decB bij ; isRight = uniq! decB bij })

freeGroupFunctorWellDefined : {b : _} {B : Set b} (decB : DecidableSet B) → {f : A → B} → Bijection f → GroupsIsomorphic (freeGroup decA) (freeGroup decB)
GroupsIsomorphic.isomorphism (freeGroupFunctorWellDefined decB {f} bij) = iso decB bij
GroupIso.groupHom (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)) = universalPropertyHom decA (freeGroup decB) λ a → freeEmbedding decB (f a)
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) refl = refl
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {x} {y} pr = Bijection.inj (inBijection decB bij) pr
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) refl = refl
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof (freeGroupFunctorWellDefined decB {f} bij)))) {x} = Bijection.surj (inBijection decB bij) x

{-
freeGroupFunctorInjective : {b : _} {B : Set b} (decB : DecidableSet B) → GroupsIsomorphic (freeGroup decA) (freeGroup decB) → Sg (A → B) (λ f → Bijection f)
freeGroupFunctorInjective decB iso = {!!}

everyGroupQuotientOfFreeGroup : {b : _} → (S : Setoid {a} {b} A) → {_+_ : A → A → A} → (G : Group S _+_) → GroupsIsomorphic G (quotientGroupByHom (freeGroup decA) (universalPropertyHom decA {!!} {!!}))
everyGroupQuotientOfFreeGroup = {!!}

everyFGGroupQuotientOfFGFreeGroup : {!!}
everyFGGroupQuotientOfFGFreeGroup = {!!}

freeGroupTorsionFree : {!!}
freeGroupTorsionFree = {!!}
-}

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
  mapNToGrpInj a (succ zero) (succ (succ y)) pr = exFalso (naughtE (transitivity (applyEquality (wordLength decA) (prependLetterInjective decA pr)) (mapNToGrpLen a (succ y))))
  mapNToGrpInj a (succ (succ x)) (succ 0) pr = exFalso (naughtE (transitivity (equalityCommutative (applyEquality (wordLength decA) (prependLetterInjective decA pr))) (mapNToGrpLen a (succ x))))
  mapNToGrpInj a (succ (succ x)) (succ (succ y)) pr = applyEquality succ (mapNToGrpInj a (succ x) (succ y) (prependLetterInjective decA pr))

freeGroupInfinite : (nonempty : A) → DedekindInfiniteSet (ReducedWord decA)
DedekindInfiniteSet.inj (freeGroupInfinite nonempty) = mapNToGrp nonempty
DedekindInfiniteSet.isInjection (freeGroupInfinite nonempty) {x} {y} = mapNToGrpInj nonempty x y
