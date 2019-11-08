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
open import Groups.Actions.Definition
open import Groups.Actions.Stabiliser
open import Groups.Groups2
open import Sets.EquivalenceRelations

module Groups.Actions.OrbitStabiliser where

orbitStabiliserEquivRel1 : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Rel A
orbitStabiliserEquivRel1 {T = T} action x g1 g2 = Setoid._∼_ T (GroupAction.action action g1 x) (GroupAction.action action g2 x)

orbitStabiliserEquivRel2 : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Rel A
orbitStabiliserEquivRel2 {T = T} {_+_ = _+_} {G = G} action x g1 g2 = Setoid._∼_ T (GroupAction.action action ((Group.inverse G g2) + g1) x) x

osEquivRel1Equiv : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Equivalence (orbitStabiliserEquivRel1 action x)
Equivalence.reflexive (osEquivRel1Equiv {T = T} action x) {a} = Equivalence.reflexive (Setoid.eq T)
Equivalence.symmetric (osEquivRel1Equiv {T = T} action x) {a} {b} = Equivalence.symmetric (Setoid.eq T)
Equivalence.transitive (osEquivRel1Equiv {T = T} action x) {a} {b} {c} = Equivalence.transitive (Setoid.eq T)

osEquivRel2Equiv : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Equivalence (orbitStabiliserEquivRel2 action x)
Equivalence.reflexive (osEquivRel2Equiv {T = T} {G = G} action x) = transitive (GroupAction.actionWellDefined1 action (Group.invLeft G)) (GroupAction.identityAction action)
  where
    open Equivalence (Setoid.eq T)
Equivalence.symmetric (osEquivRel2Equiv {S = S} {T = T} {_+_ = _+_} {G = G} gAction x) {b} {c} b=c = need
  where
    open Equivalence (Setoid.eq T)
    open Equivalence (Setoid.eq S) renaming (symmetric to symmetricS ; transitive to transitiveS ; reflexive to reflexiveS)
    open Setoid T
    open GroupAction gAction
    open Group G
    have : action ((inverse c) + b) x ∼ x
    have = b=c
    p : action (inverse (inverse b + c)) x ∼ x
    p = transitive (actionWellDefined1 (transitiveS (invContravariant G) (Group.+WellDefined G reflexiveS (invInv G)))) have
    q : action ((inverse b) + c) (action (inverse (inverse b + c)) x) ∼ action ((inverse b) + c) x
    q = actionWellDefined2 p
    r : action (((inverse b) + c) + (inverse (inverse b + c))) x ∼ action ((inverse b) + c) x
    r = transitive associativeAction q
    s : action identity x ∼ action ((inverse b) + c) x
    s = transitive (actionWellDefined1 (symmetricS invRight)) r
    need : action ((inverse b) + c) x ∼ x
    need = symmetric (transitive (symmetric identityAction) s)
Equivalence.transitive (osEquivRel2Equiv {S = S} {T = T} {_+_ = _+_} {G = G} gAction x) {a} {b} {c} a=b b=c = need
  where
    open Equivalence (Setoid.eq T)
    open Equivalence (Setoid.eq S) renaming (symmetric to symmetricS ; reflexive to reflexiveS ; transitive to transitiveS)
    open Setoid T
    open GroupAction gAction
    open Group G
    have1 : action ((inverse c) + b) x ∼ x
    have1 = b=c
    have2 : action ((inverse b) + a) x ∼ x
    have2 = a=b
    p : action ((inverse c) + b) (action (inverse b + a) x) ∼ x
    p = transitive (actionWellDefined2 have2) have1
    q : action ((inverse c + b) + (inverse b + a)) x ∼ x
    q = transitive associativeAction p
    need : action ((inverse c) + a) x ∼ x
    need = transitive (actionWellDefined1 (transitiveS (+WellDefined reflexiveS (transitiveS (symmetricS identLeft) (+WellDefined (symmetricS invRight) reflexiveS))) (fourWayAssoc G))) q

osEquivRelsEqual' : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) {g h : A} → (orbitStabiliserEquivRel2 action x) g h → (orbitStabiliserEquivRel1 action x) g h
osEquivRelsEqual' {S = S} {T = T} {_+_ = _+_} {G = G} action x {g} {h} g=h = need
  where
    open Setoid T
    open Group G
    open Equivalence eq
    open Equivalence (Setoid.eq S) renaming (symmetric to symmetricS ; transitive to transitiveS)
    have : (GroupAction.action action ((inverse h) + g) x) ∼ x
    have = g=h
    p : (GroupAction.action action (inverse h) (GroupAction.action action g x)) ∼ x
    p = transitive (symmetric (GroupAction.associativeAction action)) have
    q : (GroupAction.action action h (GroupAction.action action (inverse h) (GroupAction.action action g x))) ∼ GroupAction.action action h x
    q = GroupAction.actionWellDefined2 action p
    r : (GroupAction.action action (h + inverse h) (GroupAction.action action g x)) ∼ GroupAction.action action h x
    r = transitive (GroupAction.associativeAction action) q
    s : (GroupAction.action action identity (GroupAction.action action g x)) ∼ GroupAction.action action h x
    s = transitive (GroupAction.actionWellDefined1 action (symmetricS (Group.invRight G))) r
    need : (GroupAction.action action g x) ∼ (GroupAction.action action h x)
    need = transitive (symmetric (GroupAction.identityAction action)) s

osEquivRelsEqual : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) {g h : A} → (orbitStabiliserEquivRel1 action x) g h → (orbitStabiliserEquivRel2 action x) g h
osEquivRelsEqual {T = T} {_+_ = _+_} {G = G} action x {g} {h} g=h = need
  where
    open Setoid T
    open Group G
    open Equivalence eq
    have : (GroupAction.action action g x) ∼ (GroupAction.action action h x)
    have = g=h
    p : GroupAction.action action (inverse h) (GroupAction.action action g x) ∼ GroupAction.action action (inverse h) (GroupAction.action action h x)
    p = GroupAction.actionWellDefined2 action have
    need : (GroupAction.action action ((inverse h) + g) x) ∼ x
    need = transitive (GroupAction.associativeAction action) (transitive p (transitive (symmetric (GroupAction.associativeAction action)) (transitive (GroupAction.actionWellDefined1 action (Group.invLeft G)) (GroupAction.identityAction action))))
    
orbitStabiliserBijection : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → A → ((Stabiliser action x) && Orbit action x)
orbitStabiliserBijection action x g = stab {!GroupAction.action action ? ?!} {!!} ,, orbitElt g
  where

osBijWellDefined : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → {r s : A} → (Setoid._∼_ S r s) → Setoid._∼_ (directSumSetoid (stabiliserSetoid action x) (orbitSetoid action x)) (orbitStabiliserBijection action x r) (orbitStabiliserBijection action x s)
_&&_.fst (osBijWellDefined action x r~s) = {!!}
_&&_.snd (osBijWellDefined action x r~s) = GroupAction.actionWellDefined1 action r~s

orbitStabiliserTheorem : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → SetoidBijection S (directSumSetoid (stabiliserSetoid action x) (orbitSetoid action x)) (orbitStabiliserBijection action x)
SetoidInjection.+WellDefined (SetoidBijection.inj (orbitStabiliserTheorem {S = S} action x)) = osBijWellDefined action x
SetoidInjection.injective (SetoidBijection.inj (orbitStabiliserTheorem {S = S} action x)) {g} {h} (fst ,, gx=hx) = {!!}
SetoidSurjection.+WellDefined (SetoidBijection.surj (orbitStabiliserTheorem action x)) = osBijWellDefined action x
SetoidSurjection.surjective (SetoidBijection.surj (orbitStabiliserTheorem action x)) {stab g gx=x ,, orbitElt h} = h , ({!!} ,, {!!})
