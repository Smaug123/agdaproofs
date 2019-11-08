{-# OPTIONS --safe --warning=error --without-K #-}

open import Groups.Groups
open import Groups.Definition
open import Orders
open import Numbers.Integers.Integers
open import Setoids.Setoids
open import LogicalFormulae
open import Sets.FinSet
open import Functions
open import Sets.EquivalenceRelations
open import Numbers.Naturals.Naturals
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas
open import Groups.Homomorphisms.Image
open import Groups.Isomorphisms.Definition
open import Groups.Subgroups.Definition
open import Groups.Subgroups.Normal.Definition
open import Groups.Subgroups.Normal.Lemmas
open import Groups.Lemmas
open import Groups.Abelian.Definition
open import Groups.QuotientGroup.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Groups2 where

  groupFirstIsomorphismIso : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupHomImageElement fHom → A
  groupFirstIsomorphismIso fHom (ofElt a) = a

  groupFirstIsomorphismIsoHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupHom (imageGroup fHom) (quotientGroup G fHom) (groupFirstIsomorphismIso fHom)
  GroupHom.groupHom (groupFirstIsomorphismIsoHom {G = G} fHom) {ofElt a} {ofElt b} = Equivalence.reflexive (Setoid.eq (quotientGroupSetoid G fHom))
  GroupHom.wellDefined (groupFirstIsomorphismIsoHom {T = T} {_+G_ = _+G_} {G = G} {H = H} {f = f} fHom) {ofElt a} {ofElt b} pr = ans
    where
      open Setoid T
      open Equivalence (Setoid.eq T)
      ans : f (a +G Group.inverse G b) ∼ Group.0G H
      ans = transitive (GroupHom.groupHom fHom) (transitive (Group.+WellDefined H pr reflexive) (transitive (symmetric (GroupHom.groupHom fHom)) (transitive (GroupHom.wellDefined fHom (Group.invRight G)) (imageOfIdentityIsIdentity fHom))))

  groupFirstIsomorphismTheorem' : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupIso (imageGroup fHom) (quotientGroup G fHom) (groupFirstIsomorphismIso fHom)
  GroupIso.groupHom (groupFirstIsomorphismTheorem' fHom) = groupFirstIsomorphismIsoHom fHom
  SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (groupFirstIsomorphismTheorem' fHom))) {x} {y} x~y = GroupHom.wellDefined (groupFirstIsomorphismIsoHom fHom) {x} {y} x~y
  SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (groupFirstIsomorphismTheorem' {T = T} {H = H} {f = f} fHom))) {ofElt a} {ofElt b} pr = need
    where
      open Setoid T
      open Equivalence eq
      need : f a ∼ f b
      need = transferToRight H (transitive (transitive (Group.+WellDefined H reflexive (symmetric (homRespectsInverse fHom))) (symmetric (GroupHom.groupHom fHom))) pr)
  SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (groupFirstIsomorphismTheorem' fHom))) {x} {y} x~y = GroupHom.wellDefined (groupFirstIsomorphismIsoHom fHom) {x} {y} x~y
  SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (groupFirstIsomorphismTheorem' {G = G} fHom))) {a} = ofElt a , Equivalence.reflexive (Setoid.eq (quotientGroupSetoid G fHom))

  groupFirstIsomorphismTheorem : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupsIsomorphic (imageGroup fHom) (quotientGroup G fHom)
  groupFirstIsomorphismTheorem fHom = record { isomorphism = groupFirstIsomorphismIso fHom ; proof = groupFirstIsomorphismTheorem' fHom }

