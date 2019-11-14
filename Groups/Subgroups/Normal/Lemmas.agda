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

groupKernelGroupIsSubgroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → Subgroup G (groupKernelGroup G hom) (injectionFromKernelToGIsHom G hom)
Subgroup.fInj (groupKernelGroupIsSubgroup {S = S} {T = T} G {f = f} hom) = record { wellDefined = λ {x} {y} → GroupHom.wellDefined (injectionFromKernelToGIsHom G hom) {x} {y} ; injective = λ {x} {y} → inj {x} {y} }
  where
    inj : {x : GroupKernelElement G hom} → {y : GroupKernelElement G hom} → Setoid._∼_ S (injectionFromKernelToG G hom x) (injectionFromKernelToG G hom y) → Setoid._∼_ (groupKernel G hom) x y
    inj {kerOfElt x prX} {kerOfElt y prY} = id

groupKernelGroupIsNormalSubgroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → NormalSubgroup G (groupKernelGroup G hom) (injectionFromKernelToGIsHom G hom)
NormalSubgroup.subgroup (groupKernelGroupIsNormalSubgroup G hom) = groupKernelGroupIsSubgroup G hom
NormalSubgroup.normal (groupKernelGroupIsNormalSubgroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {f = f} hom) {g} {kerOfElt h prH} = kerOfElt ((g ·A h) ·A Group.inverse G g) ans , Equivalence.reflexive (Setoid.eq S)
  where
    open Setoid T
    open Equivalence eq
    ans : f ((g ·A h) ·A Group.inverse G g) ∼ Group.0G H
    ans = transitive (GroupHom.groupHom hom) (transitive (Group.+WellDefined H (GroupHom.groupHom hom) reflexive) (transitive (Group.+WellDefined H (Group.+WellDefined H reflexive prH) reflexive) (transitive (Group.+WellDefined H (Group.identRight H) reflexive) (transitive (symmetric (GroupHom.groupHom hom)) (transitive (GroupHom.wellDefined hom (Group.invRight G)) (imageOfIdentityIsIdentity hom))))))

abelianGroupSubgroupIsNormal : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {underG : Group S _+A_} (G : AbelianGroup underG) {H : Group T _+B_} {f : B → A} {hom : GroupHom H underG f} (s : Subgroup underG H hom) → NormalSubgroup underG H hom
NormalSubgroup.subgroup (abelianGroupSubgroupIsNormal G H) = H
NormalSubgroup.normal (abelianGroupSubgroupIsNormal {S = S} {underG = G} record { commutative = commutative } H) {g} {h} = h , transitive (+WellDefined commutative reflexive) (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight))
  where
    open Setoid S
    open Group G
    open Equivalence (Setoid.eq S)
