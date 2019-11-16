{-# OPTIONS --safe --warning=error --without-K #-}

open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Sets.EquivalenceRelations

module Setoids.Setoids where
  record Setoid {a} {b} (A : Set a) : Set (a ⊔ lsuc b) where
    infix 1 _∼_
    field
      _∼_ : A → A → Set b
      eq : Equivalence _∼_

    open Equivalence eq

    ~refl : {r : A} → (r ∼ r)
    ~refl {r} = reflexive {r}

  record Quotient {a} {b} {c} {A : Set a} {image : Set b} (S : Setoid {a} {c} A) : Set (a ⊔ b ⊔ c) where
    open Setoid S
    field
      map : A → image
      mapWellDefined : {x y : A} → x ∼ y → map x ≡ map y
      mapSurjective : Surjection map
      mapInjective : {x y : A} → map x ≡ map y → x ∼ y

  record SetoidToSet {a b c : _} {A : Set a} (S : Setoid {a} {c} A) (quotient : Set b) : Set (a ⊔ b ⊔ c) where
    open Setoid S
    field
      project : A → quotient
      wellDefined : (x y : A) → (x ∼ y) → project x ≡ project y
      surj : Surjection project
      inj : (x y : A) → project x ≡ project y → x ∼ y

  open Setoid

  reflSetoid : {a : _} (A : Set a) → Setoid A
  _∼_ (reflSetoid A) a b = a ≡ b
  Equivalence.reflexive (eq (reflSetoid A)) = refl
  Equivalence.symmetric (eq (reflSetoid A)) {b} {.b} refl = refl
  Equivalence.transitive (eq (reflSetoid A)) {b} {.b} {.b} refl refl = refl

  record SetoidInjection {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
    open Setoid S renaming (_∼_ to _∼A_)
    open Setoid T renaming (_∼_ to _∼B_)
    field
      wellDefined : {x y : A} → x ∼A y → (f x) ∼B (f y)
      injective : {x y : A} → (f x) ∼B (f y) → x ∼A y

  record SetoidSurjection {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
    open Setoid S renaming (_∼_ to _∼A_)
    open Setoid T renaming (_∼_ to _∼B_)
    field
      wellDefined : {x y : A} → x ∼A y → (f x) ∼B (f y)
      surjective : {x : B} → Sg A (λ a → f a ∼B x)

  record SetoidBijection {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
    field
      inj : SetoidInjection S T f
      surj : SetoidSurjection S T f
    wellDefined : {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)
    wellDefined = SetoidInjection.wellDefined inj

  record SetoidsBiject {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) : Set (a ⊔ b ⊔ c ⊔ d) where
    field
      bij : A → B
      bijIsBijective : SetoidBijection S T bij

  setoidInjComp : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {g : A → B} {h : B → C} → (gB : SetoidInjection S T g) (hB : SetoidInjection T U h) → SetoidInjection S U (h ∘ g)
  SetoidInjection.wellDefined (setoidInjComp gI hI) x~y = SetoidInjection.wellDefined hI (SetoidInjection.wellDefined gI x~y)
  SetoidInjection.injective (setoidInjComp gI hI) hgx~hgy = SetoidInjection.injective gI (SetoidInjection.injective hI hgx~hgy)

  setoidSurjComp : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {g : A → B} {h : B → C} → (gB : SetoidSurjection S T g) (hB : SetoidSurjection T U h) → SetoidSurjection S U (h ∘ g)
  SetoidSurjection.wellDefined (setoidSurjComp gI hI) x~y = SetoidSurjection.wellDefined hI (SetoidSurjection.wellDefined gI x~y)
  SetoidSurjection.surjective (setoidSurjComp gI hI) {x} with SetoidSurjection.surjective hI {x}
  SetoidSurjection.surjective (setoidSurjComp gI hI) {x} | a , prA with SetoidSurjection.surjective gI {a}
  SetoidSurjection.surjective (setoidSurjComp {U = U} gI hI) {x} | a , prA | b , prB = b , Equivalence.transitive (Setoid.eq U) (SetoidSurjection.wellDefined hI prB) prA
    where
      open Setoid U

  setoidBijComp : {a b c d e f : _} {A : Set a} {B : Set b} {C : Set c} {S : Setoid {a} {d} A} {T : Setoid {b} {e} B} {U : Setoid {c} {f} C} {g : A → B} {h : B → C} → (gB : SetoidBijection S T g) (hB : SetoidBijection T U h) → SetoidBijection S U (h ∘ g)
  SetoidBijection.inj (setoidBijComp gB hB) = setoidInjComp (SetoidBijection.inj gB) (SetoidBijection.inj hB)
  SetoidBijection.surj (setoidBijComp gB hB) = setoidSurjComp (SetoidBijection.surj gB) (SetoidBijection.surj hB)

  setoidIdIsBijective : {a b : _} {A : Set a} {S : Setoid {a} {b} A} → SetoidBijection S S (λ i → i)
  SetoidInjection.wellDefined (SetoidBijection.inj (setoidIdIsBijective {A = A})) = id
  SetoidInjection.injective (SetoidBijection.inj (setoidIdIsBijective {A = A})) = id
  SetoidSurjection.wellDefined (SetoidBijection.surj (setoidIdIsBijective {A = A})) = id
  SetoidSurjection.surjective (SetoidBijection.surj (setoidIdIsBijective {S = S})) {x} = x , Equivalence.reflexive (Setoid.eq S)

  record SetoidInvertible {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
    field
      fWellDefined : {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)
      inverse : B → A
      inverseWellDefined : {x y : B} → Setoid._∼_ T x y → Setoid._∼_ S (inverse x) (inverse y)
      isLeft : (b : B) → Setoid._∼_ T (f (inverse b)) b
      isRight : (a : A) → Setoid._∼_ S (inverse (f a)) a

  setoidBijectiveImpliesInvertible : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f : A → B} (bij : SetoidBijection S T f) → SetoidInvertible S T f
  SetoidInvertible.fWellDefined (setoidBijectiveImpliesInvertible bij) x~y = SetoidInjection.wellDefined (SetoidBijection.inj bij) x~y
  SetoidInvertible.inverse (setoidBijectiveImpliesInvertible bij) x with SetoidSurjection.surjective (SetoidBijection.surj bij) {x}
  SetoidInvertible.inverse (setoidBijectiveImpliesInvertible bij) x | a , b = a
  SetoidInvertible.inverseWellDefined (setoidBijectiveImpliesInvertible bij) {x} {y} x~y with SetoidSurjection.surjective (SetoidBijection.surj bij) {x}
  SetoidInvertible.inverseWellDefined (setoidBijectiveImpliesInvertible {T = T} bij) {x} {y} x~y | a , prA with SetoidSurjection.surjective (SetoidBijection.surj bij) {y}
  ... | b , prB = SetoidInjection.injective (SetoidBijection.inj bij) (Equivalence.transitive (Setoid.eq T) prA (Equivalence.transitive (Setoid.eq T) x~y (Equivalence.symmetric (Setoid.eq T) prB)))
    where
      open Setoid T
  SetoidInvertible.isLeft (setoidBijectiveImpliesInvertible bij) b with SetoidSurjection.surjective (SetoidBijection.surj bij) {b}
  ... | a , prA = prA
  SetoidInvertible.isRight (setoidBijectiveImpliesInvertible {f = f} bij) b with SetoidSurjection.surjective (SetoidBijection.surj bij) {f b}
  ... | fb , prFb = SetoidInjection.injective (SetoidBijection.inj bij) prFb

  setoidInvertibleImpliesBijective : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f : A → B} (inv : SetoidInvertible S T f) → SetoidBijection S T f
  SetoidInjection.wellDefined (SetoidBijection.inj (setoidInvertibleImpliesBijective inv)) x~y = SetoidInvertible.fWellDefined inv x~y
  SetoidInjection.injective (SetoidBijection.inj (setoidInvertibleImpliesBijective {S = S} {f = f} inv)) {x} {y} pr = Equivalence.transitive (Setoid.eq S) (Equivalence.symmetric (Setoid.eq S) (SetoidInvertible.isRight inv x)) (Equivalence.transitive (Setoid.eq S) (SetoidInvertible.inverseWellDefined inv pr) (SetoidInvertible.isRight inv y))
    where
      open Setoid S
  SetoidSurjection.wellDefined (SetoidBijection.surj (setoidInvertibleImpliesBijective inv)) x~y = SetoidInvertible.fWellDefined inv x~y
  SetoidSurjection.surjective (SetoidBijection.surj (setoidInvertibleImpliesBijective inv)) {x} = SetoidInvertible.inverse inv x , SetoidInvertible.isLeft inv x
