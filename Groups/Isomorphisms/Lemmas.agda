{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Isomorphisms.Definition
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas

module Groups.Isomorphisms.Lemmas where

groupIsosCompose : {m n o r s t : _} {A : Set m} {S : Setoid {m} {r} A} {_+A_ : A → A → A} {B : Set n} {T : Setoid {n} {s} B} {_+B_ : B → B → B} {C : Set o} {U : Setoid {o} {t} C} {_+C_ : C → C → C} {G : Group S _+A_} {H : Group T _+B_} {I : Group U _+C_} {f : A → B} {g : B → C} (fHom : GroupIso G H f) (gHom : GroupIso H I g) → GroupIso G I (g ∘ f)
GroupIso.groupHom (groupIsosCompose fHom gHom) = groupHomsCompose (GroupIso.groupHom fHom) (GroupIso.groupHom gHom)
GroupIso.bij (groupIsosCompose {A = A} {S = S} {T = T} {C = C} {U = U} {f = f} {g = g} fHom gHom) = record { inj = record { injective = λ pr → (SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij fHom))) (SetoidInjection.injective (SetoidBijection.inj (GroupIso.bij gHom)) pr) ; wellDefined = +WellDefined } ; surj = record { surjective = surj ; wellDefined = +WellDefined } }
  where
    open Setoid S renaming (_∼_ to _∼A_)
    open Setoid U renaming (_∼_ to _∼C_)
    +WellDefined : {x y : A} → (x ∼A y) → (g (f x) ∼C g (f y))
    +WellDefined = GroupHom.wellDefined (groupHomsCompose (GroupIso.groupHom fHom) (GroupIso.groupHom gHom))
    surj : {x : C} → Sg A (λ a → (g (f a) ∼C x))
    surj {x} with SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij gHom)) {x}
    surj {x} | a , prA with SetoidSurjection.surjective (SetoidBijection.surj (GroupIso.bij fHom)) {a}
    ... | b , prB = b , transitive (GroupHom.wellDefined (GroupIso.groupHom gHom) prB) prA
      where
        open Equivalence (Setoid.eq U)

--groupIsoInvertible : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d}} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : A → B} → (iso : GroupIso G H f) → GroupIso H G (Invertible.inverse (bijectionImpliesInvertible (GroupIso.bijective iso)))
--GroupHom.groupHom (GroupIso.groupHom (groupIsoInvertible {G = G} {H} {f} iso)) {x} {y} = {!!}
--  where
--    open Group G renaming (_·_ to _+G_)
--    open Group H renaming (_·_ to _+H_)
--GroupHom.wellDefined (GroupIso.groupHom (groupIsoInvertible {G = G} {H} {f} iso)) {x} {y} x∼y = {!GroupHom.wellDefined x∼y!}
--GroupIso.bijective (groupIsoInvertible {G = G} {H} {f} iso) = invertibleImpliesBijection (inverseIsInvertible (bijectionImpliesInvertible (GroupIso.bijective iso)))
