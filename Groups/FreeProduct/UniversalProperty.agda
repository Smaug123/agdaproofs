{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Setoids.Setoids
open import Groups.Definition
open import LogicalFormulae
open import Orders.WellFounded.Definition
open import Numbers.Naturals.Semiring
open import Groups.Lemmas
open import Groups.Homomorphisms.Definition
open import Groups.Homomorphisms.Lemmas

module Groups.FreeProduct.UniversalProperty {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) {a b : _} {A : I → Set a} {S : (i : I) → Setoid {a} {b} (A i)} {_+_ : (i : I) → (A i) → (A i) → A i} (decidableGroups : (i : I) → (x y : A i) → ((Setoid._∼_ (S i) x y)) || ((Setoid._∼_ (S i) x y) → False)) (G : (i : I) → Group (S i) (_+_ i)) where

open import Groups.FreeProduct.Definition decidableIndex decidableGroups G
open import Groups.FreeProduct.Setoid decidableIndex decidableGroups G
open import Groups.FreeProduct.Addition decidableIndex decidableGroups G
open import Groups.FreeProduct.Group decidableIndex decidableGroups G

universalPropertyFunction' : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {i : I} → ReducedSequenceBeginningWith i → C
universalPropertyFunction' {_+_ = _+_} H fs homs {i} (ofEmpty .i g nonZero) = fs i g
universalPropertyFunction' {_+_ = _+_} H fs homs {i} (prependLetter .i g nonZero x x₁) = (fs i g) + universalPropertyFunction' H fs homs x

universalPropertyFunction : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → ReducedSequence → C
universalPropertyFunction H fs homs empty = Group.0G H
universalPropertyFunction H fs homs (nonempty i x) = universalPropertyFunction' H fs homs x

upWellDefined : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {m n : I} → (x : ReducedSequenceBeginningWith m) (y : ReducedSequenceBeginningWith n) → (eq : =RP' x y) → Setoid._∼_ T (universalPropertyFunction H fs homs (nonempty m x)) (universalPropertyFunction H fs homs (nonempty n y))
upWellDefined H fs homs (ofEmpty m g nonZero) (ofEmpty n g₁ nonZero₁) eq with decidableIndex m n
... | inl refl = GroupHom.wellDefined (homs m) eq
upWellDefined H fs homs (prependLetter m g nonZero x x₁) (prependLetter n g₁ nonZero₁ y x₂) eq with decidableIndex m n
... | inl refl = Group.+WellDefined H (GroupHom.wellDefined (homs m) (_&&_.fst eq)) (upWellDefined H fs homs x y (_&&_.snd eq))

universalPropertyHom : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → GroupHom FreeProductGroup H (universalPropertyFunction H fs homs)
GroupHom.groupHom (universalPropertyHom H fs homs) {x} {y} = {!!}
GroupHom.wellDefined (universalPropertyHom {T = T} H fs homs) {empty} {empty} eq = Equivalence.reflexive (Setoid.eq T)
GroupHom.wellDefined (universalPropertyHom {T = T} H fs homs) {nonempty i w1} {nonempty j w2} eq = upWellDefined H fs homs w1 w2 eq

universalPropertyFunctionHasProperty : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {i : I} → (g : A i) → (nz : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → Setoid._∼_ T (fs i g) (universalPropertyFunction H fs homs (injection g nz))
universalPropertyFunctionHasProperty {T = T} H fs homs g nz = Equivalence.reflexive (Setoid.eq T)

universalPropertyFunctionUniquelyHasProperty : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → (otherFunction : ReducedSequence → C) → (isHom : GroupHom FreeProductGroup H otherFunction) → ({i : I} → (g : A i) → .(nz : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → Setoid._∼_ T (fs i g) (otherFunction (injection g nz))) → (r : ReducedSequence) → Setoid._∼_ T (otherFunction r) (universalPropertyFunction H fs homs r)
universalPropertyFunctionUniquelyHasProperty H fs homs otherFunction hom prop empty = imageOfIdentityIsIdentity hom
universalPropertyFunctionUniquelyHasProperty {T = T} H fs homs otherFunction hom prop (nonempty i (ofEmpty .i g nonZero)) = Equivalence.symmetric (Setoid.eq T) (prop g nonZero)
universalPropertyFunctionUniquelyHasProperty H fs homs otherFunction hom prop (nonempty i (prependLetter .i g nonZero x x₁)) = {!!}
