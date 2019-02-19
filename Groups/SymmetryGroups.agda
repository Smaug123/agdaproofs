{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Sets.FinSet
open import Groups.Groups
open import Groups.GroupDefinition

module Groups.SymmetryGroups where
  data SymmetryGroupElements {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
    sym : {f : A → A} → SetoidBijection S S f → SymmetryGroupElements S

  WellDefined : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) → Set (a ⊔ c ⊔ d)
  WellDefined {A = A} S T f = {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)

  data ExtensionallyEqual {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f g : A → B) (fWd : WellDefined S T f) (gWd : WellDefined S T g) : Set (a ⊔ b ⊔ c ⊔ d) where
    eq : ({x : A} → Setoid._∼_ T (f x) (g x)) → ExtensionallyEqual S T f g fWd gWd

  extensionallyEqualReflexive : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) (fWD1 fWD2 : WellDefined S T f) → ExtensionallyEqual S T f f fWD1 fWD2
  extensionallyEqualReflexive S T f fWD1 _ = eq (Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T)))

  extensionallyEqualSymmetric : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f g : A → B) (fWD : WellDefined S T f) (gWD : WellDefined S T g) → ExtensionallyEqual S T f g fWD gWD → ExtensionallyEqual S T g f gWD fWD
  extensionallyEqualSymmetric S T f g fWD gWD (eq pr) = eq (Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq T)) pr)

  extensionallyEqualTransitive : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f g h : A → B) (fWD : WellDefined S T f) (gWD : WellDefined S T g) (hWD : WellDefined S T h) → ExtensionallyEqual S T f g fWD gWD → ExtensionallyEqual S T g h gWD hWD → ExtensionallyEqual S T f h fWD hWD
  extensionallyEqualTransitive S T f g h fWD gWD hWD (eq pr1) (eq pr2) = eq (Transitive.transitive (Equivalence.transitiveEq (Setoid.eq T)) pr1 pr2)

  symmetricSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (SymmetryGroupElements S)
  Setoid._∼_ (symmetricSetoid S) (sym {f} bijF) (sym {g} bijG) = ExtensionallyEqual S S f g (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijG)
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (symmetricSetoid S))) {sym {f} bijF} = extensionallyEqualReflexive S S f (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijF)
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (symmetricSetoid S))) {sym {f} bijF} {sym {g} bijG} f~g = extensionallyEqualSymmetric S S f g (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijG) f~g
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (symmetricSetoid S))) {sym {f} bijF} {sym {g} bijG} {sym {h} bijH} f~g g~h = extensionallyEqualTransitive S S f g h (SetoidBijection.wellDefined bijF) (SetoidBijection.wellDefined bijG) (SetoidBijection.wellDefined bijH) f~g g~h

  symmetricGroupOp : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (f g : SymmetryGroupElements S) → SymmetryGroupElements S
  symmetricGroupOp (sym {f} bijF) (sym {g} bijG) = sym (setoidBijComp bijG bijF)

  symmetricGroupInv : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → SymmetryGroupElements S → SymmetryGroupElements S
  symmetricGroupInv S (sym {f} bijF) with setoidBijectiveImpliesInvertible bijF
  ... | record { inverse = inverse ; inverseWellDefined = iwd ; isLeft = isLeft ; isRight = isRight } = sym (setoidInvertibleImpliesBijective (record { fWellDefined = iwd ; inverse = f ; inverseWellDefined = SetoidInjection.wellDefined (SetoidBijection.inj bijF) ; isLeft = λ b → isRight b ; isRight = λ b → isLeft b }))

  symmetricGroupInvIsLeft : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp (symmetricGroupInv S x) x) (sym setoidIdIsBijective)
  symmetricGroupInvIsLeft {A = A} S {sym {f = f} fBij} = ExtensionallyEqual.eq ans
    where
      ans : {x : A} → Setoid._∼_ S (SetoidInvertible.inverse (setoidBijectiveImpliesInvertible fBij) (f x)) x
      ans {x} with SetoidSurjection.surjective (SetoidBijection.surj fBij) {f x}
      ans {x} | a , b = SetoidInjection.injective (SetoidBijection.inj fBij) b

  symmetricGroupInvIsRight : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp x (symmetricGroupInv S x)) (sym setoidIdIsBijective)
  symmetricGroupInvIsRight {A = A} S {sym {f = f} fBij} = ExtensionallyEqual.eq ans
    where
      ans : {x : A} → Setoid._∼_ S (f (SetoidInvertible.inverse (setoidBijectiveImpliesInvertible fBij) x)) x
      ans {x} with SetoidSurjection.surjective (SetoidBijection.surj fBij) {x}
      ans {x} | a , b = b

  symmetricGroup : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Group (symmetricSetoid S) (symmetricGroupOp {A = A})
  Group.wellDefined (symmetricGroup A) {sym {m} bijM} {sym {n} bijN} {sym {x} bijX} {sym {y} bijY} (ExtensionallyEqual.eq m~x) (ExtensionallyEqual.eq n~y) = ExtensionallyEqual.eq (transitive m~x (SetoidBijection.wellDefined bijX n~y))
    where
      open Transitive (Equivalence.transitiveEq (Setoid.eq A))
  Group.identity (symmetricGroup A) = sym setoidIdIsBijective
  Group.inverse (symmetricGroup S) = symmetricGroupInv S
  Group.multAssoc (symmetricGroup A) {sym {f} bijF} {sym {g} bijG} {sym {h} bijH} = ExtensionallyEqual.eq λ {x} → Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq A))
  Group.multIdentRight (symmetricGroup A) {sym {f} bijF} = ExtensionallyEqual.eq λ {x} → Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq A))
  Group.multIdentLeft (symmetricGroup A) {sym {f} bijF} = ExtensionallyEqual.eq λ {x} → Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq A))
  Group.invLeft (symmetricGroup S) {x} = symmetricGroupInvIsLeft S {x}
  Group.invRight (symmetricGroup S) {x} = symmetricGroupInvIsRight S {x}
