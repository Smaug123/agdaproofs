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

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Groups.Homomorphisms.Image where

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

groupHomImageInjects : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+G_ : A → A → A} {_+H_ : B → B → B} {G : Group S _+G_} {H : Group T _+H_} {f : A → B} (fHom : GroupHom G H f) → SetoidInjection (imageGroupSetoid fHom) T (groupHomImageInclusion fHom)
groupHomImageInjects {S = S} {T} {_+G_} {_+H_} {G} {H} {f} fHom = record { wellDefined = λ {x} {y} → GroupHom.wellDefined (groupHomImageIncludes fHom) {x} {y} ; injective = λ {x} {y} → inj {x} {y} }
  where
    inj : {x y : GroupHomImageElement fHom} → (Setoid._∼_ T (groupHomImageInclusion fHom x) (groupHomImageInclusion fHom y)) → Setoid._∼_ (imageGroupSetoid fHom) x y
    inj {ofElt x} {ofElt y} x~y = x~y

