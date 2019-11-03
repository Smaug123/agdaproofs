{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Homomorphisms.Definition
open import Groups.Lemmas

module Groups.Homomorphisms.Lemmas where

imageOfIdentityIsIdentity : {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {B : Set n} {T : Setoid {n} {p} B} {_·A_ : A → A → A} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} {f : A → B} → (hom : GroupHom G H f) → Setoid._∼_ T (f (Group.0G G)) (Group.0G H)
imageOfIdentityIsIdentity {S = S} {T = T} {_·A_ = _·A_} {_·B_ = _·B_} {G = G} {H = H} {f = f} hom = Equivalence.symmetric (Setoid.eq T) t
  where
    open Group H
    open Setoid T
    id2 : Setoid._∼_ S (Group.0G G) ((Group.0G G) ·A (Group.0G G))
    id2 = Equivalence.symmetric (Setoid.eq S) (Group.identRight G)
    r : f (Group.0G G) ∼ f (Group.0G G) ·B f (Group.0G G)
    s : 0G ·B f (Group.0G G) ∼ f (Group.0G G) ·B f (Group.0G G)
    t : 0G ∼ f (Group.0G G)
    t = groupsHaveRightCancellation H (f (Group.0G G)) 0G (f (Group.0G G)) s
    s = Equivalence.transitive (Setoid.eq T) identLeft r
    r = Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined hom id2) (GroupHom.groupHom hom)

groupHomsCompose : {m n o r s t : _} {A : Set m} {S : Setoid {m} {r} A} {_+A_ : A → A → A} {B : Set n} {T : Setoid {n} {s} B} {_+B_ : B → B → B} {C : Set o} {U : Setoid {o} {t} C} {_+C_ : C → C → C} {G : Group S _+A_} {H : Group T _+B_} {I : Group U _+C_} {f : A → B} {g : B → C} (fHom : GroupHom G H f) (gHom : GroupHom H I g) → GroupHom G I (g ∘ f)
GroupHom.wellDefined (groupHomsCompose {G = G} {H} {I} {f} {g} fHom gHom) {x} {y} pr = GroupHom.wellDefined gHom (GroupHom.wellDefined fHom pr)
GroupHom.groupHom (groupHomsCompose {S = S} {_+A_ = _·A_} {T = T} {U = U} {_+C_ = _·C_} {G = G} {H} {I} {f} {g} fHom gHom) {x} {y} = answer
  where
    open Group I
    answer : (Setoid._∼_ U) ((g ∘ f) (x ·A y)) ((g ∘ f) x ·C (g ∘ f) y)
    answer = (Equivalence.transitive (Setoid.eq U)) (GroupHom.wellDefined gHom (GroupHom.groupHom fHom {x} {y}) ) (GroupHom.groupHom gHom {f x} {f y})

homRespectsInverse : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_·A_ : A → A → A} {_·B_ : B → B → B} {G : Group S _·A_} {H : Group T _·B_} {underF : A → B} → (f : GroupHom G H underF) → {x : A} → Setoid._∼_ T (underF (Group.inverse G x)) (Group.inverse H (underF x))
homRespectsInverse {T = T} {_·A_ = _·A_} {_·B_ = _·B_} {G = G} {H = H} {underF = f} fHom {x} = rightInversesAreUnique H (f x) (f (Group.inverse G x)) (transitive (symmetric (GroupHom.groupHom fHom)) (transitive (GroupHom.wellDefined fHom (Group.invLeft G)) (imageOfIdentityIsIdentity fHom)))
  where
    open Setoid T
    open Equivalence eq
