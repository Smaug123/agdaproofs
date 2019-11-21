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
open import Groups.Lemmas
open import Groups.Abelian.Definition
open import Groups.QuotientGroup.Definition
open import Groups.Subgroups.Normal.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Subgroups.Normal.Lemmas where

data GroupKernelElement {a} {b} {c} {d} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) : Set (a ⊔ b ⊔ c ⊔ d) where
  kerOfElt : (x : A) → (Setoid._∼_ T (f x) (Group.0G H)) → GroupKernelElement G hom

groupKernel : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → Setoid (GroupKernelElement G hom)
Setoid._∼_ (groupKernel {S = S} G {H} {f} fHom) (kerOfElt x fx=0) (kerOfElt y fy=0) = Setoid._∼_ S x y
Equivalence.reflexive (Setoid.eq (groupKernel {S = S} G {H} {f} fHom)) {kerOfElt x x₁} = Equivalence.reflexive (Setoid.eq S)
Equivalence.symmetric (Setoid.eq (groupKernel {S = S} G {H} {f} fHom)) {kerOfElt x prX} {kerOfElt y prY} = Equivalence.symmetric (Setoid.eq S)
Equivalence.transitive (Setoid.eq (groupKernel {S = S} G {H} {f} fHom)) {kerOfElt x prX} {kerOfElt y prY} {kerOfElt z prZ} = Equivalence.transitive (Setoid.eq S)

groupKernelGroupOp : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → (GroupKernelElement G hom) → (GroupKernelElement G hom) → (GroupKernelElement G hom)
groupKernelGroupOp {T = T} {_·A_ = _+A_} G {H = H} hom (kerOfElt x prX) (kerOfElt y prY) = kerOfElt (x +A y) (transitive (GroupHom.groupHom hom) (transitive (Group.+WellDefined H prX prY) (Group.identLeft H)))
  where
    open Setoid T
    open Equivalence eq

groupKernelGroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → Group (groupKernel G hom) (groupKernelGroupOp G hom)
Group.+WellDefined (groupKernelGroup G fHom) {kerOfElt x prX} {kerOfElt y prY} {kerOfElt a prA} {kerOfElt b prB} = Group.+WellDefined G
Group.0G (groupKernelGroup G fHom) = kerOfElt (Group.0G G) (imageOfIdentityIsIdentity fHom)
Group.inverse (groupKernelGroup {T = T} G {H = H} fHom) (kerOfElt x prX) = kerOfElt (Group.inverse G x) (transitive (homRespectsInverse fHom) (transitive (inverseWellDefined H prX) (invIdent H)))
  where
    open Setoid T
    open Equivalence eq
Group.+Associative (groupKernelGroup {S = S} {_·A_ = _·A_} G fHom) {kerOfElt x prX} {kerOfElt y prY} {kerOfElt z prZ} = Group.+Associative G
Group.identRight (groupKernelGroup G fHom) {kerOfElt x prX} = Group.identRight G
Group.identLeft (groupKernelGroup G fHom) {kerOfElt x prX} = Group.identLeft G
Group.invLeft (groupKernelGroup G fHom) {kerOfElt x prX} = Group.invLeft G
Group.invRight (groupKernelGroup G fHom) {kerOfElt x prX} = Group.invRight G

injectionFromKernelToG : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → GroupKernelElement G hom → A
injectionFromKernelToG G hom (kerOfElt x _) = x

injectionFromKernelToGIsHom : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → GroupHom (groupKernelGroup G hom) G (injectionFromKernelToG G hom)
GroupHom.groupHom (injectionFromKernelToGIsHom {S = S} G hom) {kerOfElt x prX} {kerOfElt y prY} = Equivalence.reflexive (Setoid.eq S)
GroupHom.wellDefined (injectionFromKernelToGIsHom G hom) {kerOfElt x prX} {kerOfElt y prY} i = i

groupKernelGroupPred : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → A → Set d
groupKernelGroupPred {T = T} G {H = H} {f = f} hom a = Setoid._∼_ T (f a) (Group.0G H)

groupKernelGroupPredWd : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → {x y : A} → (Setoid._∼_ S x y) → (groupKernelGroupPred G hom x → groupKernelGroupPred G hom y)
groupKernelGroupPredWd {S = S} {T = T} G hom {x} {y} x=y fx=0 = Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined hom (Equivalence.symmetric (Setoid.eq S) x=y)) fx=0

groupKernelGroupIsSubgroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → Subgroup G (groupKernelGroupPred G hom)
Subgroup.closedUnderPlus (groupKernelGroupIsSubgroup {S = S} {T = T} G {H = H} hom) g=0 h=0 = Equivalence.transitive (Setoid.eq T) (GroupHom.groupHom hom) (Equivalence.transitive (Setoid.eq T) (Group.+WellDefined H g=0 h=0) (Group.identLeft H))
Subgroup.containsIdentity (groupKernelGroupIsSubgroup G hom) = imageOfIdentityIsIdentity hom
Subgroup.closedUnderInverse (groupKernelGroupIsSubgroup {S = S} {T = T} G {H = H} hom) g=0 = Equivalence.transitive (Setoid.eq T) (homRespectsInverse hom) (Equivalence.transitive (Setoid.eq T) (inverseWellDefined H g=0) (invIdent H))
Subgroup.isSubset (groupKernelGroupIsSubgroup G hom) = groupKernelGroupPredWd G hom

groupKernelGroupIsNormalSubgroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → normalSubgroup G (groupKernelGroupIsSubgroup G hom)
groupKernelGroupIsNormalSubgroup {T = T} G {H = H} hom k=0 = transitive groupHom (transitive (+WellDefined reflexive groupHom) (transitive (+WellDefined reflexive (transitive (+WellDefined k=0 reflexive) identLeft)) (transitive (symmetric groupHom) (transitive (wellDefined (Group.invRight G)) (imageOfIdentityIsIdentity hom)))))
  where
    open Setoid T
    open Group H
    open Equivalence eq
    open GroupHom hom

abelianGroupSubgroupIsNormal : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {G : Group S _+_} {pred : A → Set c} → (s : Subgroup G pred) → AbelianGroup G → normalSubgroup G s
abelianGroupSubgroupIsNormal {S = S} {_+_ = _+_} {G = G} record { isSubset = predWd ; closedUnderPlus = respectsPlus ; containsIdentity = respectsId ; closedUnderInverse = respectsInv } abelian {k} {l} prK = predWd (transitive (transitive (transitive (symmetric identLeft) (+WellDefined (symmetric invRight) reflexive)) (symmetric +Associative)) (+WellDefined reflexive commutative)) prK
  where
    open Group G
    open AbelianGroup abelian
    open Setoid S
    open Equivalence eq
