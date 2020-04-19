{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Numbers.Integers.Integers
open import Groups.Definition

module Groups.Cyclic.Definition {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) where

open Setoid S
open Group G
open Equivalence eq
open import Groups.Lemmas G

positiveEltPower : (x : A) (i : ℕ) → A
positiveEltPower x 0 = Group.0G G
positiveEltPower x (succ i) = x · (positiveEltPower x i)

positiveEltPowerWellDefinedG : (x y : A) → (x ∼ y) → (i : ℕ) → (positiveEltPower x i) ∼ (positiveEltPower y i)
positiveEltPowerWellDefinedG x y x=y 0 = reflexive
positiveEltPowerWellDefinedG x y x=y (succ i) = +WellDefined x=y (positiveEltPowerWellDefinedG x y x=y i)

positiveEltPowerCollapse : (x : A) (i j : ℕ) → Setoid._∼_ S ((positiveEltPower x i) · (positiveEltPower x j)) (positiveEltPower x (i +N j))
positiveEltPowerCollapse x zero j = Group.identLeft G
positiveEltPowerCollapse x (succ i) j = transitive (symmetric +Associative) (+WellDefined reflexive (positiveEltPowerCollapse x i j))

elementPower : (x : A) (i : ℤ) → A
elementPower x (nonneg i) = positiveEltPower x i
elementPower x (negSucc i) = Group.inverse G (positiveEltPower x (succ i))

-- TODO: move this to lemmas
elementPowerWellDefinedZ : (i j : ℤ) → (i ≡ j) → {g : A} → elementPower g i ≡ elementPower g j
elementPowerWellDefinedZ i j i=j {g} = applyEquality (elementPower g) i=j

elementPowerWellDefinedZ' : (i j : ℤ) → (i ≡ j) → {g : A} → (elementPower g i) ∼ (elementPower g j)
elementPowerWellDefinedZ' i j i=j {g} = identityOfIndiscernablesRight _∼_ reflexive (elementPowerWellDefinedZ i j i=j)

elementPowerWellDefinedG : (g h : A) → (g ∼ h) → {n : ℤ} → (elementPower g n) ∼ (elementPower h n)
elementPowerWellDefinedG g h g=h {nonneg n} = positiveEltPowerWellDefinedG g h g=h n
elementPowerWellDefinedG g h g=h {negSucc x} = inverseWellDefined (+WellDefined g=h (positiveEltPowerWellDefinedG g h g=h x))

record CyclicGroup : Set (m ⊔ n) where
  field
    generator : A
    cyclic : {a : A} → (Sg ℤ (λ i → Setoid._∼_ S (elementPower generator i) a))

