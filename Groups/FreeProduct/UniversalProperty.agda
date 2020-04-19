{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Functions.Definition
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

private
  universalPropertyFunction' : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {i : I} → ReducedSequenceBeginningWith i → C
  universalPropertyFunction' {_+_ = _+_} H fs homs {i} (ofEmpty .i g nonZero) = fs i g
  universalPropertyFunction' {_+_ = _+_} H fs homs {i} (prependLetter .i g nonZero x x₁) = (fs i g) + universalPropertyFunction' H fs homs x

universalPropertyFunction : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → ReducedSequence → C
universalPropertyFunction H fs homs empty = Group.0G H
universalPropertyFunction H fs homs (nonempty i x) = universalPropertyFunction' H fs homs x

private
  upWellDefined' : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {m n : I} → (x : ReducedSequenceBeginningWith m) (y : ReducedSequenceBeginningWith n) → (eq : =RP' x y) → Setoid._∼_ T (universalPropertyFunction H fs homs (nonempty m x)) (universalPropertyFunction H fs homs (nonempty n y))
  upWellDefined' H fs homs (ofEmpty m g nonZero) (ofEmpty n g₁ nonZero₁) eq with decidableIndex m n
  ... | inl refl = GroupHom.wellDefined (homs m) eq
  upWellDefined' H fs homs (prependLetter m g nonZero x x₁) (prependLetter n g₁ nonZero₁ y x₂) eq with decidableIndex m n
  ... | inl refl = Group.+WellDefined H (GroupHom.wellDefined (homs m) (_&&_.fst eq)) (upWellDefined' H fs homs x y (_&&_.snd eq))

  upWellDefined : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → (x : ReducedSequence) (y : ReducedSequence) → (eq : _=RP_ x y) → Setoid._∼_ T (universalPropertyFunction H fs homs x) (universalPropertyFunction H fs homs y)
  upWellDefined {T = T} H fs homs empty empty eq = Equivalence.reflexive (Setoid.eq T)
  upWellDefined H fs homs (nonempty i w1) (nonempty j w2) eq = upWellDefined' H fs homs w1 w2 eq

private
  upPrepend : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {j : I} (y : ReducedSequence) → (g : A j) .(pr : _) → Setoid._∼_ T (universalPropertyFunction H fs homs (prepend j g pr y)) ((fs j g) + universalPropertyFunction H fs homs y)
  upPrepend {T = T} H fs homs empty g pr = Equivalence.symmetric (Setoid.eq T) (Group.identRight H)
  upPrepend {T = T} H fs homs {j} (nonempty i (ofEmpty .i h nonZero)) g pr with decidableIndex j i
  ... | inr j!=i = Equivalence.reflexive (Setoid.eq T)
  ... | inl refl with decidableGroups j ((j + g) h) (Group.0G (G j))
  ... | inl x = Equivalence.transitive (Setoid.eq T) (Equivalence.symmetric (Setoid.eq T) (imageOfIdentityIsIdentity (homs j))) (Equivalence.transitive (Setoid.eq T) (Equivalence.symmetric (Setoid.eq T) (GroupHom.wellDefined (homs j) x)) (GroupHom.groupHom (homs j)))
  ... | inr x = GroupHom.groupHom (homs j)
  upPrepend {T = T} H fs homs {j} (nonempty k (prependLetter .k h nonZero y _)) g pr with decidableIndex j k
  ... | inr j!=k = Equivalence.reflexive (Setoid.eq T)
  ... | inl refl with decidableGroups j ((j + g) h) (Group.0G (G j))
  ... | inl x = transitive (symmetric (Group.identLeft H)) (transitive (Group.+WellDefined H (transitive (symmetric (imageOfIdentityIsIdentity (homs k))) (transitive (GroupHom.wellDefined (homs k) (Equivalence.symmetric (Setoid.eq (S k)) x)) (GroupHom.groupHom (homs k)))) reflexive) (symmetric (Group.+Associative H)))
    where
      open Setoid T
      open Equivalence eq
  ... | inr x = transitive (Group.+WellDefined H (GroupHom.groupHom (homs k)) reflexive) (symmetric (Group.+Associative H))
    where
      open Setoid T
      open Equivalence eq

private
  upHom : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {i : I} (x : ReducedSequenceBeginningWith i) (y : ReducedSequence) → Setoid._∼_ T (universalPropertyFunction H fs homs (plus' x y)) (universalPropertyFunction' H fs homs x + universalPropertyFunction H fs homs y)
  upHom {T = T} H fs homs (ofEmpty _ g nonZero) empty = Equivalence.symmetric (Setoid.eq T) (Group.identRight H)
  upHom {T = T} H fs homs (ofEmpty j g nonZero) (nonempty i (ofEmpty .i h nonZero1)) with decidableIndex j i
  ... | inr j!=i = Equivalence.reflexive (Setoid.eq T)
  ... | inl refl with decidableGroups j ((j + g) h) (Group.0G (G j))
  ... | inl x = Equivalence.transitive (Setoid.eq T) (Equivalence.symmetric (Setoid.eq T) (imageOfIdentityIsIdentity (homs j))) (Equivalence.transitive (Setoid.eq T) (Equivalence.symmetric (Setoid.eq T) (GroupHom.wellDefined (homs j) x)) (GroupHom.groupHom (homs j)))
  ... | inr x = GroupHom.groupHom (homs j)
  upHom {T = T} H fs homs (ofEmpty j g nonZero) (nonempty i (prependLetter .i h nonZero1 x x₁)) with decidableIndex j i
  ... | inr j!=i = Equivalence.reflexive (Setoid.eq T)
  ... | inl refl with decidableGroups j ((j + g) h) (Group.0G (G j))
  ... | inr _ = Equivalence.transitive (Setoid.eq T) (Group.+WellDefined H (GroupHom.groupHom (homs j)) (Equivalence.reflexive (Setoid.eq T))) (Equivalence.symmetric (Setoid.eq T) (Group.+Associative H))
  ... | inl eq1 = Equivalence.transitive (Setoid.eq T) (Equivalence.symmetric (Setoid.eq T) (Group.identLeft H)) (Equivalence.transitive (Setoid.eq T) (Group.+WellDefined H (Equivalence.transitive (Setoid.eq T) (Equivalence.symmetric (Setoid.eq T) (imageOfIdentityIsIdentity (homs j))) (Equivalence.transitive (Setoid.eq T) (GroupHom.wellDefined (homs j) (Equivalence.symmetric (Setoid.eq (S j)) eq1)) (GroupHom.groupHom (homs j)))) (Equivalence.reflexive (Setoid.eq T))) (Equivalence.symmetric (Setoid.eq T) (Group.+Associative H)))
  upHom {T = T} H fs homs (prependLetter j g nonZero {k} w k!=j) empty = Equivalence.transitive (Setoid.eq T) (Equivalence.transitive (Setoid.eq T) (upWellDefined H fs homs (plus' (prependLetter j g _ w k!=j) empty) (prepend j g _ (nonempty k w)) (prependWD' g nonZero (plus' w empty) (nonempty k w) (plusEmptyRight w))) (upPrepend H fs homs (nonempty k w) g nonZero)) (Equivalence.symmetric (Setoid.eq T) (Group.identRight H))
  upHom {T = T} H fs homs (prependLetter j g nonZero {k} m k!=j) (nonempty i x2) = transitive (upPrepend H fs homs (plus' m (nonempty i x2)) g nonZero) (transitive (Group.+WellDefined H reflexive (upHom H fs homs m (nonempty i x2))) (Group.+Associative H))
    where
      open Setoid T
      open Equivalence eq

universalPropertyHom : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → GroupHom FreeProductGroup H (universalPropertyFunction H fs homs)
GroupHom.wellDefined (universalPropertyHom {T = T} H fs homs) {x} {y} eq = upWellDefined H fs homs x y eq
GroupHom.groupHom (universalPropertyHom {T = T} H fs homs) {empty} {y} = Equivalence.symmetric (Setoid.eq T) (Group.identLeft H)
GroupHom.groupHom (universalPropertyHom {T = T} H fs homs) {nonempty i x} {empty} = transitive (upWellDefined H fs homs (nonempty i x +RP empty) (nonempty i x) (plusEmptyRight x)) (symmetric (Group.identRight H))
  where
    open Setoid T
    open Equivalence eq
GroupHom.groupHom (universalPropertyHom H fs homs) {nonempty i x} {nonempty j y} = upHom H fs homs x (nonempty j y)

universalPropertyFunctionHasProperty : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → {i : I} → (g : A i) → (nz : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → Setoid._∼_ T (fs i g) (universalPropertyFunction H fs homs (injection g nz))
universalPropertyFunctionHasProperty {T = T} H fs homs g nz = Equivalence.reflexive (Setoid.eq T)

private
  universalPropertyFunctionUniquelyHasPropertyLemma : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → (otherFunction : ReducedSequence → C) → (isHom : GroupHom FreeProductGroup H otherFunction) → ({i : I} → (g : A i) → .(nz : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → Setoid._∼_ T (fs i g) (otherFunction (injection g nz))) → {k l : I} (neq : (k ≡ l) → False) (r : ReducedSequenceBeginningWith l) (g : A k) .(nz : (Setoid._∼_ (S k) g (Group.0G (G k)) → False)) → Setoid._∼_ T (otherFunction (nonempty k (prependLetter k g nz r neq))) (fs k g + universalPropertyFunction' H fs homs r)
  universalPropertyFunctionUniquelyHasPropertyLemma {T = T} H fs homs otherFunction hom x {k} {l} neq (ofEmpty .l g2 nonZero) g nz = transitive (GroupHom.wellDefined hom {nonempty k (prependLetter k g nz (ofEmpty l g2 nonZero) neq)} {nonempty _ (ofEmpty k g nz) +RP nonempty _ (ofEmpty l g2 nonZero)} t) (transitive (GroupHom.groupHom hom {nonempty k (ofEmpty k g nz)} {nonempty _ (ofEmpty l g2 nonZero)}) (Group.+WellDefined H (symmetric (x g nz)) (symmetric (x g2 nonZero))))
    where
      open Setoid T
      open Equivalence eq
      t : Setoid._∼_ freeProductSetoid (nonempty k (prependLetter k g nz (ofEmpty l g2 nonZero) neq)) (prepend k g nz (nonempty l (ofEmpty l g2 nonZero)))
      t with decidableIndex k l
      ... | inl p = exFalso (neq p)
      ... | inr _ with decidableIndex k k
      ... | inr bad = exFalso (bad refl)
      ... | inl refl = Equivalence.reflexive (Setoid.eq (S k)) ,, =RP'reflex (ofEmpty l g2 _)
  universalPropertyFunctionUniquelyHasPropertyLemma {T = T} H fs homs otherFunction hom x {k} {l} neq (prependLetter .l h nonZero r pr) g nz = transitive (GroupHom.wellDefined hom {nonempty _ (prependLetter k g nz (prependLetter l h nonZero r pr) neq)} {(nonempty k (ofEmpty k g nz)) +RP (nonempty l (prependLetter l h nonZero r pr))} t) (transitive (GroupHom.groupHom hom {nonempty k (ofEmpty k g nz)} {nonempty l (prependLetter l h nonZero r pr)}) (Group.+WellDefined H (symmetric (x g nz)) (universalPropertyFunctionUniquelyHasPropertyLemma H fs homs otherFunction hom x pr r h nonZero)))
    where
      open Setoid T
      open Equivalence eq
      t : Setoid._∼_ freeProductSetoid (nonempty k (prependLetter k g nz (prependLetter l h nonZero r pr) neq)) (prepend k g nz (nonempty l (prependLetter l h nonZero r pr)))
      t with decidableIndex k l
      ... | inl bad = exFalso (neq bad)
      ... | inr k!=l with decidableIndex k k
      ... | inr bad = exFalso (bad refl)
      ... | inl refl with decidableIndex l l
      ... | inr bad = exFalso (bad refl)
      ... | inl refl = Equivalence.reflexive (Setoid.eq (S k)) ,, ((Equivalence.reflexive (Setoid.eq (S l))) ,, =RP'reflex r)

universalPropertyFunctionUniquelyHasProperty : {c d : _} {C : Set c} {T : Setoid {c} {d} C} {_+_ : C → C → C} (H : Group T _+_) → (fs : (i : I) → (A i → C)) → (homs : (i : I) → GroupHom (G i) H (fs i)) → (otherFunction : ReducedSequence → C) → (isHom : GroupHom FreeProductGroup H otherFunction) → ({i : I} → (g : A i) → .(nz : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → Setoid._∼_ T (fs i g) (otherFunction (injection g nz))) → (r : ReducedSequence) → Setoid._∼_ T (otherFunction r) (universalPropertyFunction H fs homs r)
universalPropertyFunctionUniquelyHasProperty H fs homs otherFunction hom prop empty = imageOfIdentityIsIdentity hom
universalPropertyFunctionUniquelyHasProperty {T = T} H fs homs otherFunction hom prop (nonempty i (ofEmpty .i g nonZero)) = Equivalence.symmetric (Setoid.eq T) (prop g nonZero)
universalPropertyFunctionUniquelyHasProperty {T = T} H fs homs otherFunction hom prop (nonempty i (prependLetter .i g nonZero {k} (ofEmpty .k g1 nonZero1) x1)) = transitive (GroupHom.wellDefined hom {_} {(nonempty i (ofEmpty i g nonZero)) +RP (nonempty k (ofEmpty k g1 nonZero1))} t) (transitive (GroupHom.groupHom hom {nonempty i (ofEmpty i g nonZero)}) (Group.+WellDefined H (symmetric (prop g nonZero)) (symmetric (prop g1 nonZero1))))
  where
    open Setoid T
    open Equivalence eq
    t : Setoid._∼_ freeProductSetoid (nonempty i (prependLetter i g nonZero (ofEmpty k g1 nonZero1) x1)) (prepend i g nonZero (nonempty k (ofEmpty k g1 nonZero1)))
    t with decidableIndex i k
    ... | inl p = exFalso (x1 p)
    ... | inr _ with decidableIndex i i
    ... | inr bad = exFalso (bad refl)
    ... | inl refl = Equivalence.reflexive (Setoid.eq (S i)) ,, =RP'reflex (ofEmpty k g1 nonZero1)
universalPropertyFunctionUniquelyHasProperty {T = T} H fs homs otherFunction hom prop (nonempty i (prependLetter .i g nonZero {k} (prependLetter .k g2 nonZero2 x x2) x1)) = transitive (GroupHom.wellDefined hom {nonempty i (prependLetter i g nonZero (prependLetter k g2 nonZero2 x x2) x1)} {(nonempty i (ofEmpty i g nonZero)) +RP (nonempty k (prependLetter k g2 nonZero2 x x2))} t) (transitive (GroupHom.groupHom hom {nonempty i (ofEmpty i g nonZero)} {nonempty k (prependLetter k g2 nonZero2 x x2)}) (Group.+WellDefined H (symmetric (prop g nonZero)) (universalPropertyFunctionUniquelyHasPropertyLemma H fs homs otherFunction hom prop x2 x g2 nonZero2)))
  where
    open Setoid T
    open Equivalence eq
    t : Setoid._∼_ freeProductSetoid (nonempty i (prependLetter i g nonZero (prependLetter k g2 nonZero2 x x2) x1)) (prepend i g nonZero (nonempty k (prependLetter k g2 nonZero2 x x2)))
    t with decidableIndex i k
    ... | inl x = exFalso (x1 x)
    ... | inr _ = =RP'reflex (prependLetter i g nonZero (prependLetter k g2 nonZero2 x x2) x1)
