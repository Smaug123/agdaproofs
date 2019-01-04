{-# OPTIONS --safe --warning=error #-}

open import Groups
open import Orders
open import Integers
open import Setoids
open import LogicalFormulae
open import FinSet
open import Functions
open import Naturals
open import IntegersModN
open import RingExamples
open import PrimeNumbers

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups2 where

  data GroupHomImageElement {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) : Set (a ⊔ b ⊔ c ⊔ d) where
    ofElt : (x : A) → GroupHomImageElement fHom

  imageGroupSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) → Setoid (GroupHomImageElement fHom)
  (imageGroupSetoid {T = T} {f = f} fHom Setoid.∼ ofElt b1) (ofElt b2) = Setoid._∼_ T (f b1) (f b2)
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (imageGroupSetoid {T = T} fHom))) {ofElt b1} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (imageGroupSetoid {T = T} fHom))) {ofElt b1} {ofElt b2} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq T))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (imageGroupSetoid {T = T} fHom))) {ofElt b1} {ofElt b2} {ofElt b3} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq T))

  imageGroupOp : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) → GroupHomImageElement fHom → GroupHomImageElement fHom → GroupHomImageElement fHom
  imageGroupOp {_+A_ = _+A_} fHom (ofElt a) (ofElt b) = ofElt (a +A b)

  imageGroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} (fHom : GroupHom G H f) → Group (imageGroupSetoid fHom) (imageGroupOp fHom)
  Group.wellDefined (imageGroup {T = T} {_+A_ = _+A_} {H = H} {f = f} fHom) {ofElt x} {ofElt y} {ofElt a} {ofElt b} x~a y~b = ans
    where
      open Setoid T
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
      ans : f (x +A y) ∼ f (a +A b)
      ans = transitive (GroupHom.groupHom fHom) (transitive (Group.wellDefined H x~a y~b) (symmetric (GroupHom.groupHom fHom)))
  Group.identity (imageGroup {G = G} fHom) = ofElt (Group.identity G)
  Group.inverse (imageGroup {G = G} fHom) (ofElt a) = ofElt (Group.inverse G a)
  Group.multAssoc (imageGroup {G = G} fHom) {ofElt a} {ofElt b} {ofElt c} = GroupHom.wellDefined fHom (Group.multAssoc G)
  Group.multIdentRight (imageGroup {G = G} fHom) {ofElt a} = GroupHom.wellDefined fHom (Group.multIdentRight G)
  Group.multIdentLeft (imageGroup {G = G} fHom) {ofElt a} = GroupHom.wellDefined fHom (Group.multIdentLeft G)
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
  GroupHom.groupHom (groupFirstIsomorphismIsoHom {G = G} fHom) {ofElt a} {ofElt b} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (quotientGroupSetoid G fHom)))
  GroupHom.wellDefined (groupFirstIsomorphismIsoHom {T = T} {_+G_ = _+G_} {G = G} {H = H} {f = f} fHom) {ofElt a} {ofElt b} pr = ans
    where
      open Setoid T
      open Transitive (Equivalence.transitiveEq (Setoid.eq T))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq T))
      ans : f (a +G Group.inverse G b) ∼ Group.identity H
      ans = transitive (GroupHom.groupHom fHom) (transitive (Group.wellDefined H pr reflexive) (transitive (symmetric (GroupHom.groupHom fHom)) (transitive (GroupHom.wellDefined fHom (Group.invRight G)) (imageOfIdentityIsIdentity fHom))))

  groupFirstIsomorphismTheorem' : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupIso (imageGroup fHom) (quotientGroup G fHom) (groupFirstIsomorphismIso fHom)
  GroupIso.groupHom (groupFirstIsomorphismTheorem' fHom) = groupFirstIsomorphismIsoHom fHom
  SetoidInjection.wellDefined (SetoidBijection.inj (GroupIso.bij (groupFirstIsomorphismTheorem' fHom))) {x} {y} x~y = GroupHom.wellDefined (groupFirstIsomorphismIsoHom fHom) {x} {y} x~y
  SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij (groupFirstIsomorphismTheorem' {T = T} {H = H} {f = f} fHom))) {ofElt a} {ofElt b} pr = need
    where
      open Setoid T
      open Transitive (Equivalence.transitiveEq (Setoid.eq T))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq T))
      need : f a ∼ f b
      need = transferToRight H (transitive (transitive (Group.wellDefined H reflexive (symmetric (homRespectsInverse fHom))) (symmetric (GroupHom.groupHom fHom))) pr)
  SetoidSurjection.wellDefined (SetoidBijection.surj (GroupIso.bij (groupFirstIsomorphismTheorem' fHom))) {x} {y} x~y = GroupHom.wellDefined (groupFirstIsomorphismIsoHom fHom) {x} {y} x~y
  SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij (groupFirstIsomorphismTheorem' {G = G} fHom))) {a} = ofElt a , Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (quotientGroupSetoid G fHom)))

  groupFirstIsomorphismTheorem : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → GroupsIsomorphic (imageGroup fHom) (quotientGroup G fHom)
  groupFirstIsomorphismTheorem fHom = record { isomorphism = groupFirstIsomorphismIso fHom ; proof = groupFirstIsomorphismTheorem' fHom }

  record NormalSubgroup {a} {b} {c} {d} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) {f : B → A} (hom : GroupHom H G f) : Set (a ⊔ b ⊔ c ⊔ d) where
    open Setoid S
    field
      subgroup : Subgroup G H hom
      normal : {g : A} {h : B} → Sg B (λ fromH → (g ·A (f h)) ·A (Group.inverse G g) ∼ f fromH)

  data GroupKernelElement {a} {b} {c} {d} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) : Set (a ⊔ b ⊔ c ⊔ d) where
    kerOfElt : (x : A) → (Setoid._∼_ T (f x) (Group.identity H)) → GroupKernelElement G hom

  groupKernel : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → Setoid (GroupKernelElement G hom)
  Setoid._∼_ (groupKernel {S = S} G {H} {f} fHom) (kerOfElt x fx=0) (kerOfElt y fy=0) = Setoid._∼_ S x y
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (groupKernel {S = S} G {H} {f} fHom))) {kerOfElt x x₁} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (groupKernel {S = S} G {H} {f} fHom))) {kerOfElt x prX} {kerOfElt y prY} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (groupKernel {S = S} G {H} {f} fHom))) {kerOfElt x prX} {kerOfElt y prY} {kerOfElt z prZ} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))

  groupKernelGroupOp : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → (GroupKernelElement G hom) → (GroupKernelElement G hom) → (GroupKernelElement G hom)
  groupKernelGroupOp {T = T} {_·A_ = _+A_} G {H = H} hom (kerOfElt x prX) (kerOfElt y prY) = kerOfElt (x +A y) (transitive (GroupHom.groupHom hom) (transitive (Group.wellDefined H prX prY) (Group.multIdentLeft H)))
    where
      open Setoid T
      open Transitive (Equivalence.transitiveEq (Setoid.eq T))

  groupKernelGroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → Group (groupKernel G hom) (groupKernelGroupOp G hom)
  Group.wellDefined (groupKernelGroup G fHom) {kerOfElt x prX} {kerOfElt y prY} {kerOfElt a prA} {kerOfElt b prB} = Group.wellDefined G
  Group.identity (groupKernelGroup G fHom) = kerOfElt (Group.identity G) (imageOfIdentityIsIdentity fHom)
  Group.inverse (groupKernelGroup {T = T} G {H = H} fHom) (kerOfElt x prX) = kerOfElt (Group.inverse G x) (transitive (homRespectsInverse fHom) (transitive (inverseWellDefined H prX) (invIdentity H)))
    where
      open Setoid T
      open Transitive (Equivalence.transitiveEq (Setoid.eq T))
  Group.multAssoc (groupKernelGroup {S = S} {_·A_ = _·A_} G fHom) {kerOfElt x prX} {kerOfElt y prY} {kerOfElt z prZ} = Group.multAssoc G
  Group.multIdentRight (groupKernelGroup G fHom) {kerOfElt x prX} = Group.multIdentRight G
  Group.multIdentLeft (groupKernelGroup G fHom) {kerOfElt x prX} = Group.multIdentLeft G
  Group.invLeft (groupKernelGroup G fHom) {kerOfElt x prX} = Group.invLeft G
  Group.invRight (groupKernelGroup G fHom) {kerOfElt x prX} = Group.invRight G

  injectionFromKernelToG : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → GroupKernelElement G hom → A
  injectionFromKernelToG G hom (kerOfElt x _) = x

  injectionFromKernelToGIsHom : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → GroupHom (groupKernelGroup G hom) G (injectionFromKernelToG G hom)
  GroupHom.groupHom (injectionFromKernelToGIsHom {S = S} G hom) {kerOfElt x prX} {kerOfElt y prY} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  GroupHom.wellDefined (injectionFromKernelToGIsHom G hom) {kerOfElt x prX} {kerOfElt y prY} i = i

  groupKernelGroupIsSubgroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → Subgroup G (groupKernelGroup G hom) (injectionFromKernelToGIsHom G hom)
  Subgroup.fInj (groupKernelGroupIsSubgroup {S = S} {T = T} G {f = f} hom) = record { wellDefined = λ {x} {y} → GroupHom.wellDefined (injectionFromKernelToGIsHom G hom) {x} {y} ; injective = λ {x} {y} → inj {x} {y} }
    where
      inj : {x : GroupKernelElement G hom} → {y : GroupKernelElement G hom} → Setoid._∼_ S (injectionFromKernelToG G hom x) (injectionFromKernelToG G hom y) → Setoid._∼_ (groupKernel G hom) x y
      inj {kerOfElt x prX} {kerOfElt y prY} = id

  groupKernelGroupIsNormalSubgroup : {a b c d : _} {A : Set a} {B : Set c} {S : Setoid {a} {b} A} {T : Setoid {c} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} (G : Group S _·A_) {H : Group T _·B_} {f : A → B} (hom : GroupHom G H f) → NormalSubgroup G (groupKernelGroup G hom) (injectionFromKernelToGIsHom G hom)
  NormalSubgroup.subgroup (groupKernelGroupIsNormalSubgroup G hom) = groupKernelGroupIsSubgroup G hom
  NormalSubgroup.normal (groupKernelGroupIsNormalSubgroup {S = S} {T = T} {_·A_ = _·A_} G {H = H} {f = f} hom) {g} {kerOfElt h prH} = kerOfElt ((g ·A h) ·A Group.inverse G g) ans , Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
    where
      open Setoid T
      open Transitive (Equivalence.transitiveEq (Setoid.eq T))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq T))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq T))
      ans : f ((g ·A h) ·A Group.inverse G g) ∼ Group.identity H
      ans = transitive (GroupHom.groupHom hom) (transitive (Group.wellDefined H (GroupHom.groupHom hom) reflexive) (transitive (Group.wellDefined H (Group.wellDefined H reflexive prH) reflexive) (transitive (Group.wellDefined H (Group.multIdentRight H) reflexive) (transitive (symmetric (GroupHom.groupHom hom)) (transitive (GroupHom.wellDefined hom (Group.invRight G)) (imageOfIdentityIsIdentity hom))))))

  abelianGroupSubgroupIsNormal : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {underG : Group S _+A_} (G : AbelianGroup underG) {H : Group T _+B_} {f : B → A} {hom : GroupHom H underG f} (s : Subgroup underG H hom) → NormalSubgroup underG H hom
  NormalSubgroup.subgroup (abelianGroupSubgroupIsNormal G H) = H
  NormalSubgroup.normal (abelianGroupSubgroupIsNormal {S = S} {underG = G} record { commutative = commutative } H) {g} {h} = h , transitive (wellDefined commutative reflexive) (transitive (symmetric multAssoc) (transitive (wellDefined reflexive invRight) multIdentRight))
    where
      open Setoid S
      open Group G
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))

  trivialGroup : Group (reflSetoid (FinSet 1)) λ _ _ → fzero
  Group.wellDefined trivialGroup _ _ = refl
  Group.identity trivialGroup = fzero
  Group.inverse trivialGroup _ = fzero
  Group.multAssoc trivialGroup = refl
  Group.multIdentRight trivialGroup {fzero} = refl
  Group.multIdentRight trivialGroup {fsucc ()}
  Group.multIdentLeft trivialGroup {fzero} = refl
  Group.multIdentLeft trivialGroup {fsucc ()}
  Group.invLeft trivialGroup = refl
  Group.invRight trivialGroup = refl

  identityHom : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+A_ : A → A → A} (G : Group S _+A_) → GroupHom G G id
  GroupHom.groupHom (identityHom {S = S} G) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  GroupHom.wellDefined (identityHom G) = id

