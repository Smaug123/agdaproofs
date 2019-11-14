{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Groups.Lemmas
open import Groups.Groups
open import Groups.Subgroups.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Actions.Definition
open import Groups.Groups2
open import Sets.EquivalenceRelations
open import Groups.Actions.Definition

module Groups.Actions.Stabiliser where

data Stabiliser {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) : Set (a ⊔ b ⊔ c ⊔ d) where
  stab : (g : A) → Setoid._∼_ T (GroupAction.action action g x) x → Stabiliser action x

stabiliserSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Setoid (Stabiliser action x)
Setoid._∼_ (stabiliserSetoid {S = S} action x) (stab g gx=x) (stab h hx=x) = Setoid._∼_ S g h
Equivalence.reflexive (Setoid.eq (stabiliserSetoid {S = S} action x)) {stab g _} = Equivalence.reflexive (Setoid.eq S)
Equivalence.symmetric (Setoid.eq (stabiliserSetoid {S = S} action x)) {stab g _} {stab h _} = Equivalence.symmetric (Setoid.eq S)
Equivalence.transitive (Setoid.eq (stabiliserSetoid {S = S} action x)) {stab g _} {stab h _} {stab i _} = Equivalence.transitive (Setoid.eq S)

stabiliserGroupOp : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Stabiliser action x → Stabiliser action x → Stabiliser action x
stabiliserGroupOp {T = T} {_+_ = _+_} action (stab p px=x) (stab q qx=x) = stab (p + q) (transitive (GroupAction.associativeAction action) (transitive (GroupAction.actionWellDefined2 action qx=x) px=x))
  where
    open Setoid T
    open Equivalence eq

stabiliserGroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Group (stabiliserSetoid action x) (stabiliserGroupOp action)
Group.+WellDefined (stabiliserGroup {T = T} {G = G} action {x}) {stab m mx=x} {stab n nx=x} {stab r rx=x} {stab s sx=x} m=r n=s = Group.+WellDefined G m=r n=s
  where
    open Setoid T
    open Equivalence eq
Group.0G (stabiliserGroup {G = G} action) = stab (Group.0G G) (GroupAction.identityAction action)
Group.inverse (stabiliserGroup {T = T} {_+_ = _+_} {G = G} action {x}) (stab g gx=x) = stab (Group.inverse G g) (transitive {_} {GroupAction.action action ((inverse g) + g) x} (symmetric (transitive (GroupAction.associativeAction action) (GroupAction.actionWellDefined2 action gx=x))) (transitive (GroupAction.actionWellDefined1 action invLeft) (GroupAction.identityAction action)))
  where
    open Group G
    open Setoid T
    open Equivalence eq
Group.+Associative (stabiliserGroup {G = G} action) {stab m mx=x} {stab n nx=x} {stab o ox=x} = Group.+Associative G
Group.identRight (stabiliserGroup {G = G} action) {stab m mx=x} = Group.identRight G
Group.identLeft (stabiliserGroup {G = G} action) {stab m mx=x }= Group.identLeft G
Group.invLeft (stabiliserGroup {G = G} action) {stab m mx=x} = Group.invLeft G
Group.invRight (stabiliserGroup {G = G} action) {stab m mx=x} = Group.invRight G

stabiliserInjection : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Stabiliser action x → A
stabiliserInjection action (stab g gx=x) = g

stabiliserInjectionIsHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → GroupHom (stabiliserGroup action {x}) G (stabiliserInjection action {x})
GroupHom.groupHom (stabiliserInjectionIsHom {S = S} action) {stab g gx=x} {stab h hx=x} = Equivalence.reflexive (Setoid.eq S)
GroupHom.wellDefined (stabiliserInjectionIsHom action) {stab g gx=x} {stab h hx=x} g=h = g=h

stabiliserIsSubgroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Subgroup G (stabiliserGroup action) (stabiliserInjectionIsHom action {x})
SetoidInjection.wellDefined (Subgroup.fInj (stabiliserIsSubgroup action)) {stab g gx=x} {stab h hx=x} g=h = g=h
SetoidInjection.injective (Subgroup.fInj (stabiliserIsSubgroup action)) {stab g gx=x} {stab h hx=x} g=h = g=h
