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
open import Groups.Isomorphisms.Definition
open import Groups.Subgroups.Definition
open import Groups.Subgroups.Normal.Definition
open import Groups.Subgroups.Normal.Lemmas
open import Groups.Lemmas
open import Groups.Abelian.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.FirstIsomorphismTheorem {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) where

open import Groups.Homomorphisms.Image fHom
open import Groups.Homomorphisms.Kernel fHom
open import Groups.Cosets G groupKernelIsSubgroup
open import Groups.QuotientGroup.Definition G fHom
open Setoid T
open Equivalence eq
open import Setoids.Subset T

groupFirstIsomorphismTheoremWellDefined : {x y : A} → groupKernelPred (Group.inverse G y +G x) → Setoid._∼_ (subsetSetoid imageGroupSubset) (f x , (x , reflexive)) (f y , (y , reflexive))
groupFirstIsomorphismTheoremWellDefined {x} {y} pr = transitive (symmetric (invTwice H _)) (transitive (symmetric u) (invTwice H _))
  where
    t : Setoid._∼_ T (Group.inverse H (f y) +H (f x)) (Group.0G H)
    t = transitive (transitive (Group.+WellDefined H (symmetric (homRespectsInverse fHom)) reflexive) (symmetric (GroupHom.groupHom fHom))) pr
    u : Setoid._∼_ T (Group.inverse H (Group.inverse H (f y))) (Group.inverse H (Group.inverse H (f x)))
    u = inverseWellDefined H (transferToRight' H t)

groupFirstIsomorphismTheorem : GroupsIsomorphic (cosetGroup groupKernelIsNormalSubgroup) (subgroupIsGroup H imageGroupSubgroup)
GroupsIsomorphic.isomorphism groupFirstIsomorphismTheorem x = f x , (x , reflexive)
GroupHom.groupHom (GroupIso.groupHom (GroupsIsomorphic.proof groupFirstIsomorphismTheorem)) {x} {y} = GroupHom.groupHom fHom
GroupHom.wellDefined (GroupIso.groupHom (GroupsIsomorphic.proof groupFirstIsomorphismTheorem)) {x} {y} = groupFirstIsomorphismTheoremWellDefined {x} {y}
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem))) = groupFirstIsomorphismTheoremWellDefined
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem))) fx=fy = transitive (GroupHom.groupHom fHom) (transitive (Group.+WellDefined H reflexive fx=fy) (transitive (symmetric (GroupHom.groupHom fHom)) (transitive (GroupHom.wellDefined fHom (Group.invLeft G)) (imageOfIdentityIsIdentity fHom))))
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem))) = groupFirstIsomorphismTheoremWellDefined
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem))) {b , (a , fa=b)} = a , fa=b

groupFirstIsomorphismTheoremWellDefined' : {x y : A} → f (x +G (Group.inverse G y)) ∼ Group.0G H → Setoid._∼_ (subsetSetoid imageGroupSubset) (f x , (x , reflexive)) (f y , (y , reflexive))
groupFirstIsomorphismTheoremWellDefined' {x} {y} pr = transferToRight H (transitive (symmetric (transitive (GroupHom.groupHom fHom) (Group.+WellDefined H reflexive (homRespectsInverse fHom)))) pr)

groupFirstIsomorphismTheorem' : GroupsIsomorphic (quotientGroupByHom) (subgroupIsGroup H imageGroupSubgroup)
GroupsIsomorphic.isomorphism groupFirstIsomorphismTheorem' a = f a , (a , reflexive)
GroupHom.groupHom (GroupIso.groupHom (GroupsIsomorphic.proof groupFirstIsomorphismTheorem')) {x} {y} = GroupHom.groupHom fHom
GroupHom.wellDefined (GroupIso.groupHom (GroupsIsomorphic.proof groupFirstIsomorphismTheorem')) {x} {y} = groupFirstIsomorphismTheoremWellDefined'
SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem'))) {x} {y} = groupFirstIsomorphismTheoremWellDefined' {x} {y}
SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem'))) {x} {y} fx=fy = transitive (GroupHom.groupHom fHom) (transitive (Group.+WellDefined H reflexive (homRespectsInverse fHom)) (transferToRight'' H fx=fy))
SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem'))) {x} {y} = groupFirstIsomorphismTheoremWellDefined'
SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (GroupsIsomorphic.proof groupFirstIsomorphismTheorem'))) {b , (a , fa=b)} = a , fa=b
