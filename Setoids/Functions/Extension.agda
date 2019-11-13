{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Setoids.Setoids
open import Setoids.Functions.Definition
open import Sets.EquivalenceRelations

module Setoids.Functions.Extension where

ExtensionallyEqual : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {f g : A → B} (fWd : WellDefined S T f) (gWd : WellDefined S T g) → Set (a ⊔ d)
ExtensionallyEqual {A = A} {T = T} {f = f} {g = g} fWD gWD = (∀ {x : A} → Setoid._∼_ T (f x) (g x))

extensionallyEqualReflexive : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) (fWD1 fWD2 : WellDefined S T f) → ExtensionallyEqual {S = S} {T} fWD1 fWD2
extensionallyEqualReflexive S T f fWD1 _ = Equivalence.reflexive (Setoid.eq T)

extensionallyEqualSymmetric : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f g : A → B) (fWD : WellDefined S T f) (gWD : WellDefined S T g) → ExtensionallyEqual {S = S} {T = T} fWD gWD → ExtensionallyEqual {S = S} {T} gWD fWD
extensionallyEqualSymmetric S T f g fWD gWD pr = Equivalence.symmetric (Setoid.eq T) pr

extensionallyEqualTransitive : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f g h : A → B) (fWD : WellDefined S T f) (gWD : WellDefined S T g) (hWD : WellDefined S T h) → ExtensionallyEqual {S = S} {T} fWD gWD → ExtensionallyEqual {S = S} {T} gWD hWD → ExtensionallyEqual {S = S} {T} fWD hWD
extensionallyEqualTransitive S T f g h fWD gWD hWD pr1 pr2 = Equivalence.transitive (Setoid.eq T) pr1 pr2
