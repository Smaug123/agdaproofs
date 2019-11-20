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
open import Groups.Homomorphisms.Lemmas
open import Groups.Actions.Definition
open import Sets.EquivalenceRelations

module Groups.SymmetricGroups.Lemmas where

trivialAction : {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·_ : A → A → A} {B : Set n} (G : Group S _·_) (X : Setoid {n} {p} B) → GroupAction G X
trivialAction G X = record { action = λ _ x → x ; actionWellDefined1 = λ _ → reflexive ; actionWellDefined2 = λ wd1 → wd1 ; identityAction = reflexive ; associativeAction = reflexive }
  where
    open Setoid X renaming (eq to setoidEq)
    open Equivalence (Setoid.eq X)

leftRegularAction : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) → GroupAction G S
GroupAction.action (leftRegularAction {_·_ = _·_} G) g h = g · h
  where
    open Group G
GroupAction.actionWellDefined1 (leftRegularAction {S = S} G) eq1 = +WellDefined eq1 reflexive
  where
    open Group G
    open Setoid S renaming (eq to setoidEq)
    open Equivalence setoidEq
GroupAction.actionWellDefined2 (leftRegularAction {S = S} G) {g} {x} {y} eq1 = +WellDefined reflexive eq1
  where
    open Group G
    open Setoid S
    open Equivalence eq
GroupAction.identityAction (leftRegularAction G) = identLeft
  where
    open Group G
GroupAction.associativeAction (leftRegularAction {S = S} G) = symmetric +Associative
  where
    open Group G
    open Setoid S
    open Equivalence eq

conjugationAction : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → GroupAction G S
conjugationAction {S = S} {_·_ = _·_} G = record { action = λ g h → (g · h) · (inverse g) ; actionWellDefined1 = λ gh → +WellDefined (+WellDefined gh reflexive) (inverseWellDefined G gh) ; actionWellDefined2 = λ x~y → +WellDefined (+WellDefined reflexive x~y) reflexive ; identityAction = transitive (+WellDefined reflexive (invIdent G)) (transitive identRight identLeft)  ; associativeAction = λ {x} {g} {h} → transitive (+WellDefined reflexive (invContravariant G)) (transitive +Associative (+WellDefined (transitive (symmetric +Associative) (transitive (symmetric (+Associative)) (+WellDefined reflexive +Associative))) reflexive)) }
  where
    open Group G
    open Setoid S
    open Equivalence eq

conjugationNormalSubgroupAction : {m n o p : _} {A : Set m} {B : Set o} {S : Setoid {m} {n} A} {T : Setoid {o} {p} B} {_·A_ : A → A → A} {_·B_ : B → B → B} → (G : Group S _·A_) → (H : Group T _·B_) → {underF : A → B} (f : GroupHom G H underF) → GroupAction G (quotientGroupSetoid G f)
GroupAction.action (conjugationNormalSubgroupAction {_·A_ = _·A_} G H {f} fHom) a b = a ·A (b ·A (Group.inverse G a))
GroupAction.actionWellDefined1 (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} G H {f} fHom) {g} {h} {x} g~h = ans
  where
    open Group G
    open Setoid T
    open Equivalence eq
    ans : f ((g ·A (x ·A (inverse g))) ·A inverse (h ·A (x ·A inverse h))) ∼ Group.0G H
    ans = transitive (GroupHom.wellDefined fHom (transferToRight'' G (Group.+WellDefined G g~h (Group.+WellDefined G (Equivalence.reflexive (Setoid.eq S)) (inverseWellDefined G g~h))))) (imageOfIdentityIsIdentity fHom)
GroupAction.actionWellDefined2 (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G H {f} fHom) {g} {x} {y} x~y = ans
  where
    open Group G
    open Setoid T
    open Equivalence (Setoid.eq S)
    open Equivalence (Setoid.eq T) renaming (transitive to transitiveH ; symmetric to symmetricH ; reflexive to reflexiveH)
    input : f (x ·A inverse y) ∼ Group.0G H
    input = x~y
    p1 : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ((g ·A (x ·A inverse g)) ·A (inverse (y ·A (inverse g)) ·A inverse g))
    p1 = Group.+WellDefined G reflexive (invContravariant G)
    p2 : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A (inverse (y ·A (inverse g)) ·A inverse g)) ((g ·A (x ·A inverse g)) ·A ((inverse (inverse g) ·A inverse y) ·A inverse g))
    p2 = Group.+WellDefined G reflexive (Group.+WellDefined G (invContravariant G) reflexive)
    p3 : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A ((inverse (inverse g) ·A inverse y) ·A inverse g)) (g ·A (((x ·A inverse g) ·A (inverse (inverse g) ·A inverse y)) ·A inverse g))
    p3 = symmetric (transitive (+WellDefined reflexive (symmetric +Associative)) +Associative)
    p4 : Setoid._∼_ S (g ·A (((x ·A inverse g) ·A (inverse (inverse g) ·A inverse y)) ·A inverse g)) (g ·A ((x ·A ((inverse g ·A inverse (inverse g)) ·A inverse y)) ·A inverse g))
    p4 = Group.+WellDefined G reflexive (Group.+WellDefined G (symmetric (transitive (+WellDefined reflexive (symmetric +Associative)) +Associative)) reflexive)
    p5 : Setoid._∼_ S (g ·A ((x ·A ((inverse g ·A inverse (inverse g)) ·A inverse y)) ·A inverse g)) (g ·A ((x ·A (0G ·A inverse y)) ·A inverse g))
    p5 = Group.+WellDefined G reflexive (Group.+WellDefined G (Group.+WellDefined G reflexive (Group.+WellDefined G invRight reflexive)) reflexive)
    p6 : Setoid._∼_ S  (g ·A ((x ·A (0G ·A inverse y)) ·A inverse g)) (g ·A ((x ·A inverse y) ·A inverse g))
    p6 = Group.+WellDefined G reflexive (Group.+WellDefined G (Group.+WellDefined G reflexive identLeft) reflexive)
    intermediate : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) (g ·A ((x ·A inverse y) ·A inverse g))
    intermediate = transitive p1 (transitive p2 (transitive p3 (transitive p4 (transitive p5 p6))))
    p7 : f ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ∼ f (g ·A ((x ·A inverse y) ·A inverse g))
    p7 = GroupHom.wellDefined fHom intermediate
    p8 : f (g ·A ((x ·A inverse y) ·A inverse g)) ∼ (f g) ·B (f ((x ·A inverse y) ·A inverse g))
    p8 = GroupHom.groupHom fHom
    p9 : (f g) ·B (f ((x ·A inverse y) ·A inverse g)) ∼ (f g) ·B (f (x ·A inverse y) ·B f (inverse g))
    p9 = Group.+WellDefined H reflexiveH (GroupHom.groupHom fHom)
    p10 : (f g) ·B (f (x ·A inverse y) ·B f (inverse g)) ∼ (f g) ·B (Group.0G H ·B f (inverse g))
    p10 = Group.+WellDefined H reflexiveH (Group.+WellDefined H input reflexiveH)
    p11 : (f g) ·B (Group.0G H ·B f (inverse g)) ∼ (f g) ·B (f (inverse g))
    p11 = Group.+WellDefined H reflexiveH (Group.identLeft H)
    p12 : (f g) ·B (f (inverse g)) ∼ f (g ·A (inverse g))
    p12 = symmetricH (GroupHom.groupHom fHom)
    intermediate2 : f ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ∼ (f (g ·A (inverse g)))
    intermediate2 = transitiveH p7 (transitiveH p8 (transitiveH p9 (transitiveH p10 (transitiveH p11 p12))))
    ans : f ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ∼ Group.0G H
    ans = transitiveH intermediate2 (transitiveH (GroupHom.wellDefined fHom invRight) (imageOfIdentityIsIdentity fHom))
GroupAction.identityAction (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} G H {f} fHom) {x} = ans
  where
    open Group G
    open Setoid S
    open Setoid T renaming (_∼_ to _∼T_)
    open Equivalence (Setoid.eq T)
    i : Setoid._∼_ S (x ·A inverse 0G) x
    i = Equivalence.transitive (Setoid.eq S) (+WellDefined (Equivalence.reflexive (Setoid.eq S)) (invIdent G)) identRight
    h : 0G ·A (x ·A inverse 0G) ∼ x
    h = Equivalence.transitive (Setoid.eq S) identLeft i
    g : ((0G ·A (x ·A inverse 0G)) ·A inverse x) ∼ 0G
    g = transferToRight'' G h
    ans : f ((0G ·A (x ·A inverse 0G)) ·A Group.inverse G x) ∼T Group.0G H
    ans = transitive (GroupHom.wellDefined fHom g) (imageOfIdentityIsIdentity fHom)
GroupAction.associativeAction (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} G H {f} fHom) {x} {g} {h} = ans
  where
    open Group G
    open Setoid T renaming (_∼_ to _∼T_)
    open Setoid S renaming (_∼_ to _∼S_)
    open Equivalence (Setoid.eq T) renaming (transitive to transitiveH)
    open Equivalence (Setoid.eq S) renaming (transitive to transitiveG ; symmetric to symmetricG ; reflexive to reflexiveG)
    ans : f (((g ·A h) ·A (x ·A inverse (g ·A h))) ·A inverse ((g ·A ((h ·A (x ·A inverse h)) ·A inverse g)))) ∼T Group.0G H
    ans = transitiveH (GroupHom.wellDefined fHom (transferToRight'' G (transitiveG (symmetricG +Associative) (Group.+WellDefined G reflexiveG (transitiveG (+WellDefined reflexiveG (transitiveG (+WellDefined reflexiveG (invContravariant G)) +Associative)) +Associative))))) (imageOfIdentityIsIdentity fHom)
