{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Setoids.Setoids
open import Groups.FreeGroup.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Definition
open import Decidable.Sets
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Semirings.Definition
open import Groups.Lemmas

module Groups.FreeGroup.UniversalProperty {a : _} {A : Set a} (decA : DecidableSet A) where

open import Groups.FreeGroup.Word decA
open import Groups.FreeGroup.Group decA

universalPropertyFunction : {c d : _} {C : Set c} {S : Setoid {c} {d} C} {_+_ : C → C → C} (G : Group S _+_) → (f : A → C) → ReducedWord → C
universalPropertyFunction G f empty = Group.0G G
universalPropertyFunction {_+_ = _+_} G f (prependLetter (ofLetter l) w x) = (f l) + universalPropertyFunction G f w
universalPropertyFunction {_+_ = _+_} G f (prependLetter (ofInv l) w x) = (Group.inverse G (f l)) + universalPropertyFunction G f w

private
  prepLemma : {c d : _} {C : Set c} {S : Setoid {c} {d} C} {_+_ : C → C → C} → (G : Group S _+_) → (f : A → C) → (x : ReducedWord) (l : _) → Setoid._∼_ S (universalPropertyFunction G f (prepend x (ofLetter l))) ((f l) + universalPropertyFunction G f x)
  prepLemma {S = S} G f empty l = reflexive
    where
      open Setoid S
      open Equivalence eq
  prepLemma {S = S} G f (prependLetter (ofLetter x) w pr) l = reflexive
    where
      open Setoid S
      open Equivalence eq
  prepLemma {S = S} G f (prependLetter (ofInv x) w pr) l with DecidableSet.eq decA l x
  ... | inl refl = transitive (symmetric identLeft) (transitive (+WellDefined (symmetric invRight) reflexive) (symmetric +Associative))
    where
      open Group G
      open Setoid S
      open Equivalence eq
  ... | inr l!=x = reflexive
    where
      open Setoid S
      open Equivalence eq

  prepLemma' : {c d : _} {C : Set c} {S : Setoid {c} {d} C} {_+_ : C → C → C} → (G : Group S _+_) → (f : A → C) → (x : ReducedWord) (l : _) → Setoid._∼_ S (universalPropertyFunction G f (prepend x (ofInv l))) (Group.inverse G (f l) + universalPropertyFunction G f x)
  prepLemma' {S = S} G f empty l = reflexive
    where
      open Setoid S
      open Equivalence eq
  prepLemma' {S = S} G f (prependLetter (ofLetter x) w pr) l with DecidableSet.eq decA l x
  ... | inl refl = symmetric (transitive +Associative (transitive (+WellDefined invLeft reflexive) identLeft))
    where
      open Group G
      open Setoid S
      open Equivalence eq
  ... | inr l!=x = reflexive
    where
      open Setoid S
      open Equivalence eq
  prepLemma' {S = S} G f (prependLetter (ofInv x) w pr) l = reflexive
    where
      open Setoid S
      open Equivalence eq

  homLemma : {c d : _} {C : Set c} {S : Setoid {c} {d} C} {_+_ : C → C → C} → (G : Group S _+_) → (f : A → C) → (x y : ReducedWord) → Setoid._∼_ S (universalPropertyFunction G f (x +W y)) (universalPropertyFunction G f x + universalPropertyFunction G f y)
  homLemma {S = S} G f empty y = symmetric identLeft
    where
      open Setoid S
      open Equivalence eq
      open Group G
  homLemma {S = S} G f (prependLetter (ofLetter l) x pr) y = transitive (transitive (prepLemma G f (x +W y) l) (+WellDefined reflexive (homLemma G f x y))) (+Associative {f l})
    where
      open Setoid S
      open Equivalence eq
      open Group G
  homLemma {S = S} G f (prependLetter (ofInv l) x pr) y = transitive (transitive (prepLemma' G f (x +W y) l) (+WellDefined reflexive (homLemma G f x y))) +Associative
    where
      open Setoid S
      open Equivalence eq
      open Group G

universalPropertyHom : {c d : _} {C : Set c} {S : Setoid {c} {d} C} {_+_ : C → C → C} (G : Group S _+_) → (f : A → C) → GroupHom freeGroup G (universalPropertyFunction G f)
GroupHom.groupHom (universalPropertyHom {S = S} G f) {x} {y} = homLemma G f x y
GroupHom.wellDefined (universalPropertyHom {S = S} G f) refl = Equivalence.reflexive (Setoid.eq S)

freeEmbedding : A → ReducedWord
freeEmbedding a = prependLetter (ofLetter a) empty (wordEmpty refl)

freeEmbeddingInjective : {a b : A} → freeEmbedding a ≡ freeEmbedding b → a ≡ b
freeEmbeddingInjective {a} {b} pr = ofLetterInjective (prependLetterInjective' pr)

universalPropertyDiagram : {c d : _} {C : Set c} {S : Setoid {c} {d} C} → {_+_ : C → C → C} → (G : Group S _+_) → (f : A → C) → (x : A) → Setoid._∼_ S (f x) (universalPropertyFunction G f (freeEmbedding x))
universalPropertyDiagram {S = S} G f x = symmetric (Group.identRight G)
  where
    open Setoid S
    open Equivalence eq

universalPropertyUniqueness : {c d : _} {C : Set c} {S : Setoid {c} {d} C} → {_+_ : C → C → C} → (G : Group S _+_) → (f : A → C) → {f' : ReducedWord → C} → (GroupHom freeGroup G f') → ((x : A) → Setoid._∼_ S (f x) (f' (freeEmbedding x))) → (x : ReducedWord) → Setoid._∼_ S (f' x) (universalPropertyFunction G f x)
universalPropertyUniqueness {S = S} G f {f'} f'IsHom commutes empty = imageOfIdentityIsIdentity f'IsHom
universalPropertyUniqueness {S = S} G f {f'} f'IsHom commutes (prependLetter (ofLetter a) w pr) = transitive (transitive (GroupHom.wellDefined f'IsHom (equalityCommutative (prependValid w a pr))) (GroupHom.groupHom f'IsHom)) (+WellDefined (symmetric (commutes a)) (universalPropertyUniqueness G f f'IsHom commutes w))
  where
    open Setoid S
    open Equivalence eq
    open Group G
universalPropertyUniqueness {S = S} G f {f'} f'IsHom commutes (prependLetter (ofInv a) w pr) = transitive (transitive (GroupHom.wellDefined f'IsHom (equalityCommutative (prependValid' w a pr))) (transitive (GroupHom.groupHom f'IsHom) (+WellDefined (homRespectsInverse f'IsHom) reflexive))) (+WellDefined (symmetric (inverseWellDefined G (commutes a))) (universalPropertyUniqueness G f f'IsHom commutes w))
  where
    open Setoid S
    open Equivalence eq
    open Group G

