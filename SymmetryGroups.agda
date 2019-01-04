{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Naturals
open import FinSet
open import Groups
open import GroupActions

module SymmetryGroups where
  data SymmetryGroupElements {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
    sym : {f : A → A} → SetoidBijection S S f → SymmetryGroupElements S

  data ExtensionallyEqual {a b : _} {A : Set a} {B : Set b} (f g : A → B) : Set (a ⊔ b) where
    eq : ({x : A} → (f x) ≡ (g x)) → ExtensionallyEqual f g

  extensionallyEqualReflexive : {a b : _} {A : Set a} {B : Set b} (f : A → B) → ExtensionallyEqual f f
  extensionallyEqualReflexive f = eq (λ {x} → refl)

  extensionallyEqualSymmetric : {a b : _} {A : Set a} {B : Set b} {f g : A → B} → ExtensionallyEqual f g → ExtensionallyEqual g f
  extensionallyEqualSymmetric {f} {g} (eq pr) = eq λ {x} → equalityCommutative (pr {x})

  extensionallyEqualTransitive : {a b : _} {A : Set a} {B : Set b} {f g h : A → B} → ExtensionallyEqual f g → ExtensionallyEqual g h → ExtensionallyEqual f h
  extensionallyEqualTransitive (eq pr1) (eq pr2) = eq λ {x} → transitivity pr1 pr2

  symmetricSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (SymmetryGroupElements S)
  Setoid._∼_ (symmetricSetoid A) (sym {f} bijF) (sym {g} bijG) = ExtensionallyEqual f g
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (symmetricSetoid A))) {sym {f} bijF} = extensionallyEqualReflexive f
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (symmetricSetoid A))) {sym {f} bijF} {sym {g} bijG} f~g = extensionallyEqualSymmetric f~g
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (symmetricSetoid A))) {sym {f} bijF} {sym {g} bijG} {sym {h} bijH} f~g g~h = extensionallyEqualTransitive f~g g~h

  symmetricGroupOp : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (f g : SymmetryGroupElements S) → SymmetryGroupElements S
  symmetricGroupOp (sym {f} bijF) (sym {g} bijG) = sym (setoidBijComp bijF bijG)

  symmetricGroupInv : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → SymmetryGroupElements S → SymmetryGroupElements S
  symmetricGroupInv S (sym {f} bijF) with setoidBijectiveImpliesInvertible bijF
  ... | record { inverse = inverse ; inverseWellDefined = iwd ; isLeft = isLeft ; isRight = isRight } = sym (setoidInvertibleImpliesBijective (record { fWellDefined = iwd ; inverse = f ; inverseWellDefined = SetoidInjection.wellDefined (SetoidBijection.inj bijF) ; isLeft = λ b → isRight b ; isRight = λ b → isLeft b }))

  symmetricGroupInvIsLeft : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp (symmetricGroupInv S x) x) (sym setoidIdIsBijective)
  symmetricGroupInvIsLeft {A = A} S {sym fBij} = ExtensionallyEqual.eq λ {x} → {!ans (sym fBij)!}
    where
      ans : (f : A → A) → (bij : SetoidBijection S S f) → f (symmetricGroupInv S (sym fBij) x) ≡ sym fBij
      ans elt = {!!}

  symmetricGroupInvIsRight : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp x (symmetricGroupInv S x)) (sym setoidIdIsBijective)
  symmetricGroupInvIsRight S {sym x} = {!!}

  symmetricGroup : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Group (symmetricSetoid S) (symmetricGroupOp {A = A})
  Group.wellDefined (symmetricGroup A) {sym {m} bijM} {sym {n} bijN} {sym {x} bijX} {sym {y} bijY} (ExtensionallyEqual.eq m~x) (ExtensionallyEqual.eq n~y) = ExtensionallyEqual.eq λ {z} → transitivity (applyEquality n m~x) n~y
  Group.identity (symmetricGroup A) = sym setoidIdIsBijective
  Group.inverse (symmetricGroup S) = symmetricGroupInv S
  Group.multAssoc (symmetricGroup A) {sym {f} bijF} {sym {g} bijG} {sym {h} bijH} = ExtensionallyEqual.eq λ {x} → refl
  Group.multIdentRight (symmetricGroup A) {sym {f} bijF} = ExtensionallyEqual.eq λ {x} → refl
  Group.multIdentLeft (symmetricGroup A) {sym {f} bijF} = ExtensionallyEqual.eq λ {x} → refl
  Group.invLeft (symmetricGroup S) {x} = symmetricGroupInvIsLeft S {x}
  Group.invRight (symmetricGroup S) {x} = symmetricGroupInvIsRight S {x}

  actionInducesHom : {a b c d : _} {A : Set a} {S : Setoid {a} {c} A} {_+_ : A → A → A} {G : Group S _+_} {B : Set b} {X : Setoid {b} {d} B} → (GroupAction G X) → SymmetryGroupElements X
  actionInducesHom = {!!}
