{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Setoids.DirectSum
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Abelian.Definition
open import Groups.Homomorphisms.Definition
open import Groups.DirectSum.Definition
open import Groups.Subgroups.Definition
open import Groups.Isomorphisms.Definition

module Groups.Abelian.Lemmas where

directSumAbelianGroup : {m n o p : _} → {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} {underG : Group S _·A_} {underH : Group T _·B_} (G : AbelianGroup underG) (h : AbelianGroup underH) → (AbelianGroup (directSumGroup underG underH))
AbelianGroup.commutative (directSumAbelianGroup {A = A} {B} G H) = AbelianGroup.commutative G ,, AbelianGroup.commutative H

subgroupOfAbelianIsAbelian : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : B → A} {fHom : GroupHom H G f} → Subgroup G H fHom → AbelianGroup G → AbelianGroup H
AbelianGroup.commutative (subgroupOfAbelianIsAbelian {S = S} {_+B_ = _+B_} {fHom = fHom} record { fInj = fInj } record { commutative = commutative }) {x} {y} = SetoidInjection.injective fInj (transitive (GroupHom.groupHom fHom) (transitive commutative (symmetric (GroupHom.groupHom fHom))))
  where
    open Setoid S
    open Equivalence eq

abelianIsGroupProperty : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} → GroupsIsomorphic G H → AbelianGroup H → AbelianGroup G
abelianIsGroupProperty iso abH = subgroupOfAbelianIsAbelian {fHom = GroupIso.groupHom (GroupsIsomorphic.proof iso)} (record { fInj = SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof iso)) }) abH
