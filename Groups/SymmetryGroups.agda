{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Sets.FinSet
open import Groups.GroupDefinition

module Groups.SymmetryGroups where
  data SymmetryGroupElements {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
    sym : {f : A → A} → SetoidBijection S S f → SymmetryGroupElements S

  record WellDefined {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
    field
      wd : {r s : A} → Setoid._∼_ S r s → Setoid._∼_ T (f r) (f s)

  record ExtensionallyEqual {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f : A → B} {g : A → B} (fWD : WellDefined {S = S} {T = T} f) (gWD : WellDefined {S = S} {T = T} g) : Set (a ⊔ b ⊔ c ⊔ d) where
    field
      eq : {x : A} → Setoid._∼_ T (f x) (g x)

  bijectionWellDefined : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {f : A → A} → SetoidBijection S S f → WellDefined {S = S} {S} f
  WellDefined.wd (bijectionWellDefined record { inj = record { wellDefined = wellDefined ; injective = injective } ; surj = surj }) {r} {s} r=s = wellDefined {r} {s} r=s

  extensionallyEqualReflexive : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f : A → B} → (fWD : WellDefined {S = S} {T = T} f) → ExtensionallyEqual {S = S} {T = T} fWD fWD
  ExtensionallyEqual.eq (extensionallyEqualReflexive {T = T} f) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq T))

  extensionallyEqualSymmetric : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f g : A → B} → {fWD : WellDefined {S = S} {T = T} f} → {gWD : WellDefined {S = S} {T = T} g} → ExtensionallyEqual fWD gWD → ExtensionallyEqual gWD fWD
  ExtensionallyEqual.eq (extensionallyEqualSymmetric {T = T} {f} {g} record { eq = eq }) = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq T)) eq

  extensionallyEqualTransitive : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f g h : A → B} {fWD : WellDefined {S = S} {T = T} f} {gWD : WellDefined {S = S} {T = T} g} {hWD : WellDefined {S = S} {T = T} h} → ExtensionallyEqual fWD gWD → ExtensionallyEqual gWD hWD → ExtensionallyEqual fWD hWD
  ExtensionallyEqual.eq (extensionallyEqualTransitive {T = T} record { eq = f=g } record { eq = g=h }) = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq T)) f=g g=h

  symmetricSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (SymmetryGroupElements S)
  (symmetricSetoid S Setoid.∼ sym f) (sym g) = ExtensionallyEqual {S = S} {T = S} (bijectionWellDefined f) (bijectionWellDefined g)
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (symmetricSetoid S))) {sym f} = extensionallyEqualReflexive (bijectionWellDefined f)
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (symmetricSetoid S))) {sym b} {sym c} b=c = extensionallyEqualSymmetric b=c
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (symmetricSetoid S))) {sym a} {sym b} {sym c} a=b b=c = extensionallyEqualTransitive a=b b=c

  symmetricGroupOp : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (f g : SymmetryGroupElements S) → SymmetryGroupElements S
  symmetricGroupOp (sym {f} bijF) (sym {g} bijG) = sym (setoidBijComp bijG bijF)

  symmetricGroupInv : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → SymmetryGroupElements S → SymmetryGroupElements S
  symmetricGroupInv S (sym {f} bijF) with setoidBijectiveImpliesInvertible bijF
  ... | record { inverse = inverse ; inverseWellDefined = iwd ; isLeft = isLeft ; isRight = isRight } = sym (setoidInvertibleImpliesBijective (record { fWellDefined = iwd ; inverse = f ; inverseWellDefined = SetoidInjection.wellDefined (SetoidBijection.inj bijF) ; isLeft = λ b → isRight b ; isRight = λ b → isLeft b }))

  symmetricGroupInvIsLeft : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp (symmetricGroupInv S x) x) (sym setoidIdIsBijective)
  symmetricGroupInvIsLeft {A = A} S {sym {f} fBij} = record { eq = λ {x} → ans x }
    where
      ans : (x : A) → Setoid._∼_ S ((SetoidInvertible.inverse (setoidBijectiveImpliesInvertible fBij) (f x))) x
      ans x with SetoidSurjection.surjective (SetoidBijection.surj fBij) {f x}
      ans x | a , b = SetoidInjection.injective (SetoidBijection.inj fBij) b

  symmetricGroupInvIsRight : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → {x : SymmetryGroupElements S} → Setoid._∼_ (symmetricSetoid S) (symmetricGroupOp x (symmetricGroupInv S x)) (sym setoidIdIsBijective)
  ExtensionallyEqual.eq (symmetricGroupInvIsRight {A = A} S {sym {f} fBij}) {x} = ans x
    where
      ans : (x : A) → Setoid._∼_ S (f (SetoidInvertible.inverse (setoidBijectiveImpliesInvertible fBij) x)) x
      ans x with SetoidSurjection.surjective (SetoidBijection.surj fBij) {x}
      ans x | a , b = b

  symmetricGroup : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Group (symmetricSetoid S) (symmetricGroupOp {A = A})
  Group.wellDefined (symmetricGroup {A = A} S) {sym {m} mBij} {sym {n} nBij} {sym {x} xBij} {sym {y} yBij} record { eq = eqMX } record { eq = eqNY } = record { eq = λ {a} → transitive ((WellDefined.wd (bijectionWellDefined mBij)) eqNY) eqMX }
    where
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
  Group.identity (symmetricGroup A) = sym {f = λ i → i} (setoidIdIsBijective)
  Group.inverse (symmetricGroup A) = symmetricGroupInv A
  ExtensionallyEqual.eq (Group.multAssoc (symmetricGroup A) {sym {a} aBij} {sym {b} bBij} {sym {c} cBij}) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq A))
  Group.multIdentRight (symmetricGroup A) {sym {a} aBij} = record { eq = λ {x} → Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq A)) }
  Group.multIdentLeft (symmetricGroup A) {sym {a} aBij} = record { eq = λ {x} → Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq A)) }
  Group.invLeft (symmetricGroup A) {x} = symmetricGroupInvIsLeft A {x}
  Group.invRight (symmetricGroup A) {x} = symmetricGroupInvIsRight A {x}
