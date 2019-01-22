{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Sets.FinSet
open import Groups.GroupDefinition
open import Groups.GroupsLemmas
open import Groups.Groups

module Groups.GroupActions where
    record GroupAction {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·_ : A → A → A} {B : Set n} (G : Group S _·_) (X : Setoid {n} {p} B) : Set (m ⊔ n ⊔ o ⊔ p) where
      open Group G
      open Setoid S renaming (_∼_ to _∼G_)
      open Setoid X renaming (_∼_ to _∼X_)
      field
        action : A → B → B
        actionWellDefined1 : {g h : A} → {x : B} → (g ∼G h) → action g x ∼X action h x
        actionWellDefined2 : {g : A} → {x y : B} → (x ∼X y) → action g x ∼X action g y
        identityAction : {x : B} → action identity x ∼X x
        associativeAction : {x : B} → {g h : A} → action (g · h) x ∼X action g (action h x)

    trivialAction : {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·_ : A → A → A} {B : Set n} (G : Group S _·_) (X : Setoid {n} {p} B) → GroupAction G X
    trivialAction G X = record { action = λ _ x → x ; actionWellDefined1 = λ _ → reflexive ; actionWellDefined2 = λ wd1 → wd1 ; identityAction = reflexive ; associativeAction = reflexive }
      where
        open Setoid X
        open Equivalence eq
        open Reflexive reflexiveEq

    leftRegularAction : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} (G : Group S _·_) → GroupAction G S
    GroupAction.action (leftRegularAction {_·_ = _·_} G) g h = g · h
      where
        open Group G
    GroupAction.actionWellDefined1 (leftRegularAction {S = S} G) eq1 = wellDefined eq1 reflexive
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Reflexive reflexiveEq
    GroupAction.actionWellDefined2 (leftRegularAction {S = S} G) {g} {x} {y} eq1 = wellDefined reflexive eq1
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Reflexive reflexiveEq
    GroupAction.identityAction (leftRegularAction G) = multIdentLeft
      where
        open Group G
    GroupAction.associativeAction (leftRegularAction {S = S} G) = symmetric multAssoc
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Symmetric symmetricEq

    conjugationAction : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_·_ : A → A → A} → (G : Group S _·_) → GroupAction G S
    conjugationAction {S = S} {_·_ = _·_} G = record { action = λ g h → (g · h) · (inverse g) ; actionWellDefined1 = λ gh → wellDefined (wellDefined gh reflexive) (inverseWellDefined G gh) ; actionWellDefined2 = λ x~y → wellDefined (wellDefined reflexive x~y) reflexive ; identityAction = transitive (wellDefined reflexive (invIdentity G)) (transitive multIdentRight multIdentLeft)  ; associativeAction = λ {x} {g} {h} → transitive (wellDefined reflexive (invContravariant G)) (transitive multAssoc (wellDefined (fourWayAssoc' G) reflexive)) }
      where
        open Group G
        open Setoid S
        open Equivalence eq
        open Reflexive reflexiveEq
        open Transitive transitiveEq

    conjugationNormalSubgroupAction : {m n o p : _} {A : Set m} {B : Set o} {S : Setoid {m} {n} A} {T : Setoid {o} {p} B} {_·A_ : A → A → A} {_·B_ : B → B → B} → (G : Group S _·A_) → (H : Group T _·B_) → {underF : A → B} (f : GroupHom G H underF) → GroupAction G (quotientGroupSetoid G f)
    GroupAction.action (conjugationNormalSubgroupAction {_·A_ = _·A_} G H {f} fHom) a b = a ·A (b ·A (Group.inverse G a))
    GroupAction.actionWellDefined1 (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} G H {f} fHom) {g} {h} {x} g~h = ans
      where
        open Group G
        open Setoid T
        open Equivalence (Setoid.eq T)
        open Transitive transitiveEq
        open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
        open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
        ans : f ((g ·A (x ·A (inverse g))) ·A inverse (h ·A (x ·A inverse h))) ∼ Group.identity H
        ans = transitive (GroupHom.wellDefined fHom (transferToRight'' G (Group.wellDefined G g~h (Group.wellDefined G reflexive (inverseWellDefined G g~h))))) (imageOfIdentityIsIdentity fHom)
    GroupAction.actionWellDefined2 (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} G H {f} fHom) {g} {x} {y} x~y = ans
      where
        open Group G
        open Setoid T
        open Equivalence (Setoid.eq T)
        open Transitive transitiveEq
        open Transitive (Equivalence.transitiveEq (Setoid.eq S)) renaming (transitive to transitiveG)
        open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
        open Symmetric (Equivalence.symmetricEq (Setoid.eq T)) renaming (symmetric to symmetricH)
        open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
        open Reflexive (Equivalence.reflexiveEq (Setoid.eq T)) renaming (reflexive to reflexiveH)
        input : f (x ·A inverse y) ∼ Group.identity H
        input = x~y
        p1 : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ((g ·A (x ·A inverse g)) ·A (inverse (y ·A (inverse g)) ·A inverse g))
        p1 = Group.wellDefined G reflexive (invContravariant G)
        p2 : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A (inverse (y ·A (inverse g)) ·A inverse g)) ((g ·A (x ·A inverse g)) ·A ((inverse (inverse g) ·A inverse y) ·A inverse g))
        p2 = Group.wellDefined G reflexive (Group.wellDefined G (invContravariant G) reflexive)
        p3 : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A ((inverse (inverse g) ·A inverse y) ·A inverse g)) (g ·A (((x ·A inverse g) ·A (inverse (inverse g) ·A inverse y)) ·A inverse g))
        p3 = symmetric (fourWayAssoc G)
        p4 : Setoid._∼_ S (g ·A (((x ·A inverse g) ·A (inverse (inverse g) ·A inverse y)) ·A inverse g)) (g ·A ((x ·A ((inverse g ·A inverse (inverse g)) ·A inverse y)) ·A inverse g))
        p4 = Group.wellDefined G reflexive (Group.wellDefined G (symmetric (fourWayAssoc G)) reflexive)
        p5 : Setoid._∼_ S (g ·A ((x ·A ((inverse g ·A inverse (inverse g)) ·A inverse y)) ·A inverse g)) (g ·A ((x ·A (identity ·A inverse y)) ·A inverse g))
        p5 = Group.wellDefined G reflexive (Group.wellDefined G (Group.wellDefined G reflexive (Group.wellDefined G invRight reflexive)) reflexive)
        p6 : Setoid._∼_ S  (g ·A ((x ·A (identity ·A inverse y)) ·A inverse g)) (g ·A ((x ·A inverse y) ·A inverse g))
        p6 = Group.wellDefined G reflexive (Group.wellDefined G (Group.wellDefined G reflexive multIdentLeft) reflexive)
        intermediate : Setoid._∼_ S ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) (g ·A ((x ·A inverse y) ·A inverse g))
        intermediate = transitiveG p1 (transitiveG p2 (transitiveG p3 (transitiveG p4 (transitiveG p5 p6))))
        p7 : f ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ∼ f (g ·A ((x ·A inverse y) ·A inverse g))
        p7 = GroupHom.wellDefined fHom intermediate
        p8 : f (g ·A ((x ·A inverse y) ·A inverse g)) ∼ (f g) ·B (f ((x ·A inverse y) ·A inverse g))
        p8 = GroupHom.groupHom fHom
        p9 : (f g) ·B (f ((x ·A inverse y) ·A inverse g)) ∼ (f g) ·B (f (x ·A inverse y) ·B f (inverse g))
        p9 = Group.wellDefined H reflexiveH (GroupHom.groupHom fHom)
        p10 : (f g) ·B (f (x ·A inverse y) ·B f (inverse g)) ∼ (f g) ·B (Group.identity H ·B f (inverse g))
        p10 = Group.wellDefined H reflexiveH (Group.wellDefined H input reflexiveH)
        p11 : (f g) ·B (Group.identity H ·B f (inverse g)) ∼ (f g) ·B (f (inverse g))
        p11 = Group.wellDefined H reflexiveH (Group.multIdentLeft H)
        p12 : (f g) ·B (f (inverse g)) ∼ f (g ·A (inverse g))
        p12 = symmetricH (GroupHom.groupHom fHom)
        intermediate2 : f ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ∼ (f (g ·A (inverse g)))
        intermediate2 = transitive p7 (transitive p8 (transitive p9 (transitive p10 (transitive p11 p12))))
        ans : f ((g ·A (x ·A inverse g)) ·A inverse (g ·A (y ·A inverse g))) ∼ Group.identity H
        ans = transitive intermediate2 (transitive (GroupHom.wellDefined fHom invRight) (imageOfIdentityIsIdentity fHom))
    GroupAction.identityAction (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} G H {f} fHom) {x} = ans
      where
        open Group G
        open Setoid S
        open Setoid T renaming (_∼_ to _∼T_)
        open Equivalence (Setoid.eq T)
        open Transitive transitiveEq
        i : Setoid._∼_ S (x ·A inverse identity) x
        i = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) (wellDefined (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))) (invIdentity G)) multIdentRight
        h : identity ·A (x ·A inverse identity) ∼ x
        h = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) multIdentLeft i
        g : ((identity ·A (x ·A inverse identity)) ·A inverse x) ∼ identity
        g = transferToRight'' G h
        ans : f ((identity ·A (x ·A inverse identity)) ·A Group.inverse G x) ∼T Group.identity H
        ans = transitive (GroupHom.wellDefined fHom g) (imageOfIdentityIsIdentity fHom)
    GroupAction.associativeAction (conjugationNormalSubgroupAction {S = S} {T = T} {_·A_ = _·A_} G H {f} fHom) {x} {g} {h} = ans
      where
        open Group G
        open Setoid T renaming (_∼_ to _∼T_)
        open Setoid S renaming (_∼_ to _∼S_)
        open Transitive (Equivalence.transitiveEq (Setoid.eq T)) renaming (transitive to transitiveH)
        open Transitive (Equivalence.transitiveEq (Setoid.eq S)) renaming (transitive to transitiveG)
        open Symmetric (Equivalence.symmetricEq (Setoid.eq S)) renaming (symmetric to symmetricG)
        open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
        ans : f (((g ·A h) ·A (x ·A inverse (g ·A h))) ·A inverse ((g ·A ((h ·A (x ·A inverse h)) ·A inverse g)))) ∼T Group.identity H
        ans = transitiveH (GroupHom.wellDefined fHom (transferToRight'' G (transitiveG (symmetricG multAssoc) (Group.wellDefined G reflexive (transitiveG (wellDefined reflexive (transitiveG (wellDefined reflexive (invContravariant G)) multAssoc)) multAssoc))))) (imageOfIdentityIsIdentity fHom)

