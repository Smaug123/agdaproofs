{-# OPTIONS --warning=error --safe --without-K #-}

open import Functions.Definition
open import Groups.Definition
open import Groups.Homomorphisms.Definition
open import Setoids.Setoids
open import Sets.EquivalenceRelations
open import Groups.Lemmas
open import Groups.QuotientGroup.Definition
open import Groups.Homomorphisms.Lemmas

module Groups.QuotientGroup.Lemmas {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} (G : Group S _+A_) (H : Group T _+B_) {f : A → B} (fHom : GroupHom G H f) where

quotientGroupLemma : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {underf : A → B} → (f : GroupHom G H underf) → {x y : A} → Setoid._∼_ T (underf x) (underf y) → Setoid._∼_ (quotientGroupSetoid G f) x y
quotientGroupLemma {S = S} {T = T} G {H = H} fHom {x} {y} fx=fy = transitive (GroupHom.groupHom fHom) (transitive (Group.+WellDefined H (Equivalence.reflexive (Setoid.eq T)) (homRespectsInverse fHom)) (transferToRight'' H fx=fy))
  where
    open Group G
    open Setoid T
    open Equivalence eq

quotientGroupLemma' : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} → {underf : A → B} → (f : GroupHom G H underf) → {x y : A} → Setoid._∼_ (quotientGroupSetoid G f) x y → Setoid._∼_ T (underf x) (underf y)
quotientGroupLemma' {S = S} {T = T} G {H = H} f fx=fy = transferToRight H (transitive (transitive (Group.+WellDefined H (Equivalence.reflexive (Setoid.eq T)) (symmetric (homRespectsInverse f))) (symmetric (GroupHom.groupHom f))) fx=fy)
  where
    open Group G
    open Setoid T
    open Equivalence eq

projectionMapIsGroupHom : GroupHom G (quotientGroupByHom G fHom) id
GroupHom.groupHom projectionMapIsGroupHom {x} {y} = quotientGroupLemma G fHom (Equivalence.reflexive (Setoid.eq T))
GroupHom.wellDefined projectionMapIsGroupHom x=y = quotientGroupLemma G fHom (GroupHom.wellDefined fHom x=y)
