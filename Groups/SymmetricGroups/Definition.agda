{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Groups
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Setoids.Functions.Extension

module Groups.SymmetricGroups.Definition where

data SymmetryGroupElements {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
  sym : {f : A → A} → SetoidBijection S S f → SymmetryGroupElements S

symmetricSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (SymmetryGroupElements S)
Setoid._∼_ (symmetricSetoid S) (sym {f} bijF) (sym {g} bijG) = ExtensionallyEqual {S = S} {S} (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijG)
Equivalence.reflexive (Setoid.eq (symmetricSetoid S)) {sym {f} bijF} = extensionallyEqualReflexive S S f (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijF)
Equivalence.symmetric (Setoid.eq (symmetricSetoid S)) {sym {f} bijF} {sym {g} bijG} f~g = extensionallyEqualSymmetric S S f g (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijG) f~g
Equivalence.transitive (Setoid.eq (symmetricSetoid S)) {sym {f} bijF} {sym {g} bijG} {sym {h} bijH} f~g g~h = extensionallyEqualTransitive S S f g h (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijG) (SetoidBijection.wellDefined bijH) f~g g~h

symmetricGroupOp : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (f g : SymmetryGroupElements S) → SymmetryGroupElements S
symmetricGroupOp (sym {f} bijF) (sym {g} bijG) = sym (setoidBijComp bijG bijF)

symmetricGroupInv : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → SymmetryGroupElements S → SymmetryGroupElements S
symmetricGroupInv S (sym {f} bijF) with setoidBijectiveImpliesInvertible bijF
... | record { inverse = inverse ; inverseWellDefined = iwd ; isLeft = isLeft ; isRight = isRight } = sym (setoidInvertibleImpliesBijective (record { fWellDefined = iwd ; inverse = f ; inverseWellDefined = SetoidInjection.wellDefined (SetoidBijection.inj bijF) ; isLeft = λ b → isRight b ; isRight = λ b → isLeft b }))

symmetricGroupInvIsLeft : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp (symmetricGroupInv S x) x) (sym setoidIdIsBijective)
symmetricGroupInvIsLeft {A = A} S {sym {f = f} fBij} = ans
  where
    ans : {x : A} → Setoid._∼_ S (SetoidInvertible.inverse (setoidBijectiveImpliesInvertible fBij) (f x)) x
    ans {x} with SetoidSurjection.surjective (SetoidBijection.surj fBij) {f x}
    ans {x} | a , b = SetoidInjection.injective (SetoidBijection.inj fBij) b

symmetricGroupInvIsRight : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp x (symmetricGroupInv S x)) (sym setoidIdIsBijective)
symmetricGroupInvIsRight {A = A} S {sym {f = f} fBij} = ans
  where
    ans : {x : A} → Setoid._∼_ S (f (SetoidInvertible.inverse (setoidBijectiveImpliesInvertible fBij) x)) x
    ans {x} with SetoidSurjection.surjective (SetoidBijection.surj fBij) {x}
    ans {x} | a , b = b

symmetricGroup : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Group (symmetricSetoid S) (symmetricGroupOp {A = A})
Group.+WellDefined (symmetricGroup A) {sym {m} bijM} {sym {n} bijN} {sym {x} bijX} {sym {y} bijY} m~x n~y = transitive m~x (SetoidBijection.wellDefined bijX n~y)
  where
    open Equivalence (Setoid.eq A)
Group.0G (symmetricGroup A) = sym setoidIdIsBijective
Group.inverse (symmetricGroup S) = symmetricGroupInv S
Group.+Associative (symmetricGroup A) {sym {f} bijF} {sym {g} bijG} {sym {h} bijH} = Equivalence.reflexive (Setoid.eq A)
Group.identRight (symmetricGroup A) {sym {f} bijF} = Equivalence.reflexive (Setoid.eq A)
Group.identLeft (symmetricGroup A) {sym {f} bijF} = Equivalence.reflexive (Setoid.eq A)
Group.invLeft (symmetricGroup S) {x} = symmetricGroupInvIsLeft S {x}
Group.invRight (symmetricGroup S) {x} = symmetricGroupInvIsRight S {x}
