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

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Groups2 where

  data GroupHomImageElement {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) : Set (a ⊔ b ⊔ c ⊔ d) where
    ofElt : (x : A) → GroupHomImageElement fHom

  imageGroupSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) → Setoid (GroupHomImageElement fHom)
  (imageGroupSetoid {T = T} {f = f} fHom Setoid.∼ ofElt b1) (ofElt b2) = Setoid._∼_ T (f b1) (f b2)
  Equivalence.reflexive (Setoid.eq (imageGroupSetoid {T = T} fHom)) {ofElt b1} = Equivalence.reflexive (Setoid.eq T)
  Equivalence.symmetric (Setoid.eq (imageGroupSetoid {T = T} fHom)) {ofElt b1} {ofElt b2} = Equivalence.symmetric (Setoid.eq T)
  Equivalence.transitive (Setoid.eq (imageGroupSetoid {T = T} fHom)) {ofElt b1} {ofElt b2} {ofElt b3} = Equivalence.transitive (Setoid.eq T)

  imageGroupOp : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) → GroupHomImageElement fHom → GroupHomImageElement fHom → GroupHomImageElement fHom
  imageGroupOp {_+A_ = _+A_} fHom (ofElt a) (ofElt b) = ofElt (a +A b)

  imageGroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) → Group (imageGroupSetoid fHom) (imageGroupOp fHom)
  Group.+WellDefined (imageGroup {T = T} {_+A_ = _+A_} {H = H} {f = f} fHom) {ofElt x} {ofElt y} {ofElt a} {ofElt b} x~a y~b = ans
    where
      open Setoid T
      open Equivalence eq
      ans : f (x +A y) ∼ f (a +A b)
      ans = transitive (GroupHom.groupHom fHom) (transitive (Group.+WellDefined H x~a y~b) (symmetric (GroupHom.groupHom fHom)))
  Group.0G (imageGroup {G = G} fHom) = ofElt (Group.0G G)
  Group.inverse (imageGroup {G = G} fHom) (ofElt a) = ofElt (Group.inverse G a)
  Group.+Associative (imageGroup {G = G} fHom) {ofElt a} {ofElt b} {ofElt c} = GroupHom.wellDefined fHom (Group.+Associative G)
  Group.identRight (imageGroup {G = G} fHom) {ofElt a} = GroupHom.wellDefined fHom (Group.identRight G)
  Group.identLeft (imageGroup {G = G} fHom) {ofElt a} = GroupHom.wellDefined fHom (Group.identLeft G)
  Group.invLeft (imageGroup {G = G} fHom) {ofElt a} = GroupHom.wellDefined fHom (Group.invLeft G)
  Group.invRight (imageGroup {G = G} fHom) {ofElt a} = GroupHom.wellDefined fHom (Group.invRight G)

  groupHomImageInclusion : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupHomImageElement fHom → B
  groupHomImageInclusion {f = f} fHom (ofElt x) = f x

  groupHomImageIncludes : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupHom (imageGroup fHom) H (groupHomImageInclusion fHom)
  GroupHom.groupHom (groupHomImageIncludes fHom) {ofElt x} {ofElt y} = GroupHom.groupHom fHom
  GroupHom.wellDefined (groupHomImageIncludes fHom) {ofElt x} {ofElt y} x~y = x~y

  groupHomImageIsSubgroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → Subgroup H (imageGroup fHom) (groupHomImageIncludes fHom)
  Subgroup.fInj (groupHomImageIsSubgroup {S = S} {T} {_+G_} {_+H_} {G} {H} {f} fHom) = record { wellDefined = λ {x} {y} → GroupHom.wellDefined (groupHomImageIncludes fHom) {x} {y} ; injective = λ {x} {y} → inj {x} {y} }
    where
      inj : {x y : GroupHomImageElement fHom} → (Setoid._∼_ T (groupHomImageInclusion fHom x) (groupHomImageInclusion fHom y)) → Setoid._∼_ (imageGroupSetoid fHom) x y
      inj {ofElt x} {ofElt y} x~y = x~y

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

  record NormalSubgroup {a} {b} {c} {d} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) {f : B → A} (hom : GroupHom H G f) : Set (a ⊔ b ⊔ c ⊔ d) where
    open Setoid S
    field
      subgroup : Subgroup G H hom
      normal : {g : A} {h : B} → Sg B (λ fromH → (g ·A (f h)) ·A (Group.inverse G g) ∼ f fromH)

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

  trivialGroup : Group (reflSetoid (FinSet 1)) λ _ _ → fzero
  Group.+WellDefined trivialGroup _ _ = refl
  Group.0G trivialGroup = fzero
  Group.inverse trivialGroup _ = fzero
  Group.+Associative trivialGroup = refl
  Group.identRight trivialGroup {fzero} = refl
  Group.identRight trivialGroup {fsucc ()}
  Group.identLeft trivialGroup {fzero} = refl
  Group.identLeft trivialGroup {fsucc ()}
  Group.invLeft trivialGroup = refl
  Group.invRight trivialGroup = refl

  identityHom : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ : A → A → A} (G : Group S _+A_) → GroupHom G G id
  GroupHom.groupHom (identityHom {S = S} G) = Equivalence.reflexive (Setoid.eq S)
  GroupHom.wellDefined (identityHom G) = id
