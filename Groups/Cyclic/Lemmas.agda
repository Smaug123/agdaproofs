{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Definition
open import Numbers.Integers.Integers
open import Numbers.Integers.Addition
open import Sets.FinSet.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Groups
open import Groups.Subgroups.Definition
open import Groups.Lemmas
open import Groups.Subgroups.Definition
open import Groups.Abelian.Definition
open import Groups.Definition
open import Groups.Cyclic.Definition
open import Groups.Cyclic.DefinitionLemmas
open import Semirings.Definition
open import Rings.Definition

module Groups.Cyclic.Lemmas {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) where

elementPowerHom : (x : A) → GroupHom ℤGroup G (λ i → elementPower G x i)
GroupHom.groupHom (elementPowerHom x) {a} {b} = symmetric (elementPowerCollapse G x a b)
  where
    open Equivalence (Setoid.eq S)
GroupHom.wellDefined (elementPowerHom x) {.y} {y} refl = reflexive
  where
    open Equivalence (Setoid.eq S)

subgroupOfCyclicIsCyclic : {c : _} {pred : A → Set c} → (sub : Subgroup G pred) → CyclicGroup G → CyclicGroup (subgroupIsGroup G sub)
CyclicGroup.generator (subgroupOfCyclicIsCyclic {pred = pred} sub record { generator = g ; cyclic = cyclic }) = {!!}
  where
    leastPowerInGroup : (bound : ℕ) → ℕ
    leastPowerInGroup bound = {!!}
CyclicGroup.cyclic (subgroupOfCyclicIsCyclic sub cyc) = {!!}

-- Prefer to prove that subgroup of cyclic is cyclic, then deduce this like with abelian groups
{-
cyclicIsGroupProperty : {m n o p : _} {A : Set m} {B : Set o} {S : Setoid {m} {n} A} {T : Setoid {o} {p} B} {_+_ : A → A → A} {_*_ : B → B → B} {G : Group S _+_} {H : Group T _*_} → GroupsIsomorphic G H → CyclicGroup G → CyclicGroup H
CyclicGroup.generator (cyclicIsGroupProperty {H = H} iso G) = GroupsIsomorphic.isomorphism iso (CyclicGroup.generator G)
CyclicGroup.cyclic (cyclicIsGroupProperty {H = H} iso G) {a} with GroupIso.surj (GroupsIsomorphic.proof iso) {a}
CyclicGroup.cyclic (cyclicIsGroupProperty {H = H} iso G) {a} | a' , b with CyclicGroup.cyclic G {a'}
... | pow , prPow = pow , {!!}
-}

cyclicGroupIsAbelian : (cyclic : CyclicGroup G) → AbelianGroup G
AbelianGroup.commutative (cyclicGroupIsAbelian record { generator = generator ; cyclic = cyclic }) {a} {b} with cyclic {a}
... | bl with cyclic {b}
AbelianGroup.commutative (cyclicGroupIsAbelian record { generator = generator ; cyclic = cyclic }) {a} {b} | nA , prA | nB , prB = transitive (+WellDefined (symmetric prA) (symmetric prB)) (transitive (symmetric (GroupHom.groupHom (elementPowerHom generator) {nA} {nB})) (transitive (transitive (elementPowerWellDefinedZ' G (nA +Z nB) (nB +Z nA) (Ring.groupIsAbelian ℤRing {nA} {nB}) {generator}) (GroupHom.groupHom (elementPowerHom generator) {nB} {nA})) (+WellDefined prB prA)))
  where
    open Setoid S
    open Equivalence eq
    open Group G
