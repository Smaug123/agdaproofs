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
open import Groups.SymmetryGroups

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

    actionPermutation : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} → (action : GroupAction G T) → (g : A) → SymmetryGroupElements T
    actionPermutation {B = B} {T = T} {_+_ = _+_} {G = G} action g = sym {f = λ x → (GroupAction.action action g x)} (record { inj = record { injective = inj ; wellDefined = GroupAction.actionWellDefined2 action } ; surj = record { surjective = surj ; wellDefined = GroupAction.actionWellDefined2 action } })
      where
        open Setoid T
        open Reflexive (Equivalence.reflexiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)
        open Transitive (Equivalence.transitiveEq eq)
        open Group G
        inj : {x y : B} → (Setoid._∼_ T (GroupAction.action action g x) (GroupAction.action action g y)) → Setoid._∼_ T x y
        inj {x} {y} gx=gy = transitive (symmetric (GroupAction.identityAction action)) (transitive (transitive (symmetric (GroupAction.actionWellDefined1 action (invLeft {g}))) (transitive (transitive (GroupAction.associativeAction action) (transitive (GroupAction.actionWellDefined2 action gx=gy) (symmetric (GroupAction.associativeAction action)))) (GroupAction.actionWellDefined1 action (invLeft {g})))) (GroupAction.identityAction action))
        surj : {x : B} → Sg B (λ a → GroupAction.action action g a ∼ x)
        surj {x} = GroupAction.action action (inverse g) x , transitive (symmetric (GroupAction.associativeAction action)) (transitive (GroupAction.actionWellDefined1 action invRight) (GroupAction.identityAction action))

    actionPermutationMapIsHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) → GroupHom G (symmetricGroup T) (actionPermutation action)
    GroupHom.groupHom (actionPermutationMapIsHom {T = T} action) = record { eq = λ {z} → GroupAction.associativeAction action }
      where
        open Setoid T
        open Reflexive (Equivalence.reflexiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)
        open Transitive (Equivalence.transitiveEq eq)
    GroupHom.wellDefined (actionPermutationMapIsHom action) x=y = record { eq = λ {z} → GroupAction.actionWellDefined1 action x=y }

    data Stabiliser {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) : Set (a ⊔ b ⊔ c ⊔ d) where
      stab : (g : A) → Setoid._∼_ T (GroupAction.action action g x) x → Stabiliser action x

    stabiliserSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Setoid (Stabiliser action x)
    Setoid._∼_ (stabiliserSetoid {S = S} action x) (stab g gx=x) (stab h hx=x) = Setoid._∼_ S g h
    Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (stabiliserSetoid {S = S} action x))) {stab g _} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
    Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (stabiliserSetoid {S = S} action x))) {stab g _} {stab h _} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
    Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (stabiliserSetoid {S = S} action x))) {stab g _} {stab h _} {stab i _} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))

    stabiliserGroupOp : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Stabiliser action x → Stabiliser action x → Stabiliser action x
    stabiliserGroupOp {T = T} {_+_ = _+_} action (stab p px=x) (stab q qx=x) = stab (p + q) (transitive (GroupAction.associativeAction action) (transitive (GroupAction.actionWellDefined2 action qx=x) px=x))
      where
        open Setoid T
        open Reflexive (Equivalence.reflexiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)
        open Transitive (Equivalence.transitiveEq eq)

    stabiliserGroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Group (stabiliserSetoid action x) (stabiliserGroupOp action)
    Group.wellDefined (stabiliserGroup {T = T} {G = G} action {x}) {stab m mx=x} {stab n nx=x} {stab r rx=x} {stab s sx=x} m=r n=s = Group.wellDefined G m=r n=s
      where
        open Setoid T
        open Reflexive (Equivalence.reflexiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)
        open Transitive (Equivalence.transitiveEq eq)
    Group.identity (stabiliserGroup {G = G} action) = stab (Group.identity G) (GroupAction.identityAction action)
    Group.inverse (stabiliserGroup {T = T} {_+_ = _+_} {G = G} action {x}) (stab g gx=x) = stab (Group.inverse G g) (transitive {_} {GroupAction.action action ((inverse g) + g) x} (symmetric (transitive (GroupAction.associativeAction action) (GroupAction.actionWellDefined2 action gx=x))) (transitive (GroupAction.actionWellDefined1 action invLeft) (GroupAction.identityAction action)))
      where
        open Group G
        open Setoid T
        open Reflexive (Equivalence.reflexiveEq eq)
        open Symmetric (Equivalence.symmetricEq eq)
        open Transitive (Equivalence.transitiveEq eq)
    Group.multAssoc (stabiliserGroup {G = G} action) {stab m mx=x} {stab n nx=x} {stab o ox=x} = Group.multAssoc G
    Group.multIdentRight (stabiliserGroup {G = G} action) {stab m mx=x} = Group.multIdentRight G
    Group.multIdentLeft (stabiliserGroup {G = G} action) {stab m mx=x }= Group.multIdentLeft G
    Group.invLeft (stabiliserGroup {G = G} action) {stab m mx=x} = Group.invLeft G
    Group.invRight (stabiliserGroup {G = G} action) {stab m mx=x} = Group.invRight G

    stabiliserInjection : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Stabiliser action x → A
    stabiliserInjection action (stab g gx=x) = g

    stabiliserInjectionIsHom : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → GroupHom (stabiliserGroup action {x}) G (stabiliserInjection action {x})
    GroupHom.groupHom (stabiliserInjectionIsHom {S = S} action) {stab g gx=x} {stab h hx=x} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
    GroupHom.wellDefined (stabiliserInjectionIsHom action) {stab g gx=x} {stab h hx=x} g=h = g=h

    stabiliserIsSubgroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) {x : B} → Subgroup G (stabiliserGroup action) (stabiliserInjectionIsHom action {x})
    SetoidInjection.wellDefined (Subgroup.fInj (stabiliserIsSubgroup action)) {stab g gx=x} {stab h hx=x} g=h = g=h
    SetoidInjection.injective (Subgroup.fInj (stabiliserIsSubgroup action)) {stab g gx=x} {stab h hx=x} g=h = g=h

    orbitStabiliserEquivRel1 : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Rel A
    orbitStabiliserEquivRel1 {T = T} action x g1 g2 = Setoid._∼_ T (GroupAction.action action g1 x) (GroupAction.action action g2 x)

    orbitStabiliserEquivRel2 : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Rel A
    orbitStabiliserEquivRel2 {T = T} {_+_ = _+_} {G = G} action x g1 g2 = Setoid._∼_ T (GroupAction.action action ((Group.inverse G g2) + g1) x) x

    osEquivRel1Equiv : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Equivalence (orbitStabiliserEquivRel1 action x)
    Reflexive.reflexive (Equivalence.reflexiveEq (osEquivRel1Equiv {T = T} action x)) {a} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T))
    Symmetric.symmetric (Equivalence.symmetricEq (osEquivRel1Equiv {T = T} action x)) {a} {b} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq T))
    Transitive.transitive (Equivalence.transitiveEq (osEquivRel1Equiv {T = T} action x)) {a} {b} {c} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq T))

    osEquivRel2Equiv : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Equivalence (orbitStabiliserEquivRel2 action x)
    Reflexive.reflexive (Equivalence.reflexiveEq (osEquivRel2Equiv {T = T} {G = G} action x)) = transitive (GroupAction.actionWellDefined1 action (Group.invLeft G)) (GroupAction.identityAction action)
      where
        open Transitive (Equivalence.transitiveEq (Setoid.eq T))
    Symmetric.symmetric (Equivalence.symmetricEq (osEquivRel2Equiv {S = S} {T = T} {_+_ = _+_} {G = G} gAction x)) {b} {c} b=c = need
      where
        open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
        open Symmetric (Equivalence.symmetricEq (Setoid.eq S)) renaming (symmetric to symmetricS)
        open Transitive (Equivalence.transitiveEq (Setoid.eq T))
        open Transitive (Equivalence.transitiveEq (Setoid.eq S)) renaming (transitive to transitiveS)
        open Reflexive (Equivalence.reflexiveEq (Setoid.eq S)) renaming (reflexive to reflexiveS)
        open Setoid T
        open GroupAction gAction
        open Group G
        have : action ((inverse c) + b) x ∼ x
        have = b=c
        p : action (inverse (inverse b + c)) x ∼ x
        p = transitive (actionWellDefined1 (transitiveS (invContravariant G) (Group.wellDefined G reflexiveS (invInv G)))) have
        q : action ((inverse b) + c) (action (inverse (inverse b + c)) x) ∼ action ((inverse b) + c) x
        q = actionWellDefined2 p
        r : action (((inverse b) + c) + (inverse (inverse b + c))) x ∼ action ((inverse b) + c) x
        r = transitive associativeAction q
        s : action identity x ∼ action ((inverse b) + c) x
        s = transitive (actionWellDefined1 (symmetricS invRight)) r
        need : action ((inverse b) + c) x ∼ x
        need = symmetric (transitive (symmetric identityAction) s)
    Transitive.transitive (Equivalence.transitiveEq (osEquivRel2Equiv {S = S} {T = T} {_+_ = _+_} {G = G} gAction x)) {a} {b} {c} a=b b=c = need
      where
        open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
        open Symmetric (Equivalence.symmetricEq (Setoid.eq S)) renaming (symmetric to symmetricS)
        open Transitive (Equivalence.transitiveEq (Setoid.eq T))
        open Transitive (Equivalence.transitiveEq (Setoid.eq S)) renaming (transitive to transitiveS)
        open Reflexive (Equivalence.reflexiveEq (Setoid.eq S)) renaming (reflexive to reflexiveS)
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
        need = transitive (actionWellDefined1 (transitiveS (wellDefined reflexiveS (transitiveS (symmetricS multIdentLeft) (wellDefined (symmetricS invRight) reflexiveS))) (fourWayAssoc G))) q

    osEquivRelsEqual' : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) {g h : A} → (orbitStabiliserEquivRel2 action x) g h → (orbitStabiliserEquivRel1 action x) g h
    osEquivRelsEqual' {S = S} {T = T} {_+_ = _+_} {G = G} action x {g} {h} g=h = need
      where
        open Setoid T
        open Group G
        open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
        open Symmetric (Equivalence.symmetricEq (Setoid.eq S)) renaming (symmetric to symmetricS)
        open Transitive (Equivalence.transitiveEq (Setoid.eq T))
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
        open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
        open Transitive (Equivalence.transitiveEq (Setoid.eq T))
        have : (GroupAction.action action g x) ∼ (GroupAction.action action h x)
        have = g=h
        p : GroupAction.action action (inverse h) (GroupAction.action action g x) ∼ GroupAction.action action (inverse h) (GroupAction.action action h x)
        p = GroupAction.actionWellDefined2 action have
        need : (GroupAction.action action ((inverse h) + g) x) ∼ x
        need = transitive (GroupAction.associativeAction action) (transitive p (transitive (symmetric (GroupAction.associativeAction action)) (transitive (GroupAction.actionWellDefined1 action (Group.invLeft G)) (GroupAction.identityAction action))))

    data Orbit {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) : Set (a ⊔ b ⊔ c ⊔ d) where
      orbitElt : (g : A) → Orbit action x

    orbitSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → Setoid (Orbit action x)
    Setoid._∼_ (orbitSetoid {T = T} action x) (orbitElt a) (orbitElt b) = Setoid._∼_ T (GroupAction.action action a x) (GroupAction.action action b x)
    Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (orbitSetoid {T = T} action x))) {orbitElt g} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T))
    Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (orbitSetoid {T = T} action x))) {orbitElt g} {orbitElt h} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq T))
    Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (orbitSetoid {T = T} action x))) {orbitElt g} {orbitElt h} {orbitElt i} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq T))

    orbitStabiliserBijection : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → A → ((Stabiliser action x) && Orbit action x)
    orbitStabiliserBijection action x g = stab {!g!} {!!} ,, orbitElt g

    osBijWellDefined : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → {r s : A} → (Setoid._∼_ S r s) → Setoid._∼_ (directSumSetoid (stabiliserSetoid action x) (orbitSetoid action x)) (orbitStabiliserBijection action x r) (orbitStabiliserBijection action x s)
    _&&_.fst (osBijWellDefined action x r~s) = {!!}
    _&&_.snd (osBijWellDefined action x r~s) = GroupAction.actionWellDefined1 action r~s

    orbitStabiliserTheorem : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+_ : A → A → A} {G : Group S _+_} (action : GroupAction G T) (x : B) → SetoidBijection S (directSumSetoid (stabiliserSetoid action x) (orbitSetoid action x)) (orbitStabiliserBijection action x)
    SetoidInjection.wellDefined (SetoidBijection.inj (orbitStabiliserTheorem {S = S} action x)) = osBijWellDefined action x
    SetoidInjection.injective (SetoidBijection.inj (orbitStabiliserTheorem {S = S} action x)) {g} {h} (fst ,, gx=hx) = {!!}
    SetoidSurjection.wellDefined (SetoidBijection.surj (orbitStabiliserTheorem action x)) = osBijWellDefined action x
    SetoidSurjection.surjective (SetoidBijection.surj (orbitStabiliserTheorem action x)) {stab g gx=x ,, orbitElt h} = h , ({!!} ,, {!!})
