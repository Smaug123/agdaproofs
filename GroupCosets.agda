{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Naturals
open import Integers
open import FinSet
open import Groups

module GroupCosets where
  data GroupCoset {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : B → A} {fHom : GroupHom H G f} (subgrp : Subgroup G H fHom) : Set (a ⊔ b ⊔ c ⊔ d) where
    cosetOfElt : (x : A) → GroupCoset subgrp

  groupCosetSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : B → A} {fHom : GroupHom H G f} (subgrp : Subgroup G H fHom) → Setoid (GroupCoset subgrp)
  Setoid._∼_ (groupCosetSetoid {A = A} {S = S} {_+A_ = _+A_} {G = G} subgrp) (cosetOfElt x) (cosetOfElt y) = Sg (A && A) (λ p → x +A (_&&_.fst p) ∼ y +A (_&&_.snd p))
    where
      open Setoid S
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (groupCosetSetoid {S = S} {G = G} subgrp))) {cosetOfElt x} = (identity ,, identity) , transitive (multIdentRight) (symmetric multIdentRight)
    where
      open Group G
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (groupCosetSetoid {S = S} subgrp))) {cosetOfElt x} {cosetOfElt y} ((xMul ,, yMul) , pr) = (yMul ,, xMul) , Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) pr
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (groupCosetSetoid {S = S} {_+A_ = _+A_} {G = G} subgrp))) {cosetOfElt x} {cosetOfElt y} {cosetOfElt z} ((xMul ,, yMul) , pr) ((yMul' ,, zMul) , pr2) = (((xMul +A (inverse yMul)) +A yMul') ,, zMul) , transitive (transitive multAssoc (wellDefined (transitive multAssoc (transitive (wellDefined pr reflexive) (transitive (symmetric multAssoc) (transitive (wellDefined reflexive invRight) multIdentRight)))) reflexive)) pr2
    where
      open Group G
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Reflexive (Equivalence.reflexiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)

  groupCosetBijection : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+A_ : A → A → A} {_+B_ : B → B → B} {G : Group S _+A_} {H : Group T _+B_} {f : B → A} {fHom : GroupHom H G f} (subgrp : Subgroup G H fHom) → SetoidsBiject T (groupCosetSetoid subgrp)
  SetoidsBiject.bij (groupCosetBijection {f = f} subgrp) x = cosetOfElt (f x)
  SetoidInjection.wellDefined (SetoidBijection.inj (SetoidsBiject.bijIsBijective (groupCosetBijection {S = S} {G = G} {fHom = fHom} subgrp))) x~y = (identity ,, identity) , transitive multIdentRight (transitive (GroupHom.wellDefined fHom x~y) (symmetric multIdentRight))
    where
      open Group G
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
  SetoidInjection.injective (SetoidBijection.inj (SetoidsBiject.bijIsBijective (groupCosetBijection {S = S} {_+A_ = _+A_} {G = G} {f = f} subgrp))) {x} {y} ((xH ,, yH) , b) = {!!}
  SetoidSurjection.wellDefined (SetoidBijection.surj (SetoidsBiject.bijIsBijective (groupCosetBijection {S = S} {G = G} {fHom = fHom} subgrp))) x~y = (identity ,, identity) , transitive multIdentRight (transitive (GroupHom.wellDefined fHom x~y) (symmetric multIdentRight))
    where
      open Group G
      open Setoid S
      open Transitive (Equivalence.transitiveEq eq)
      open Symmetric (Equivalence.symmetricEq eq)
  SetoidSurjection.surjective (SetoidBijection.surj (SetoidsBiject.bijIsBijective (groupCosetBijection subgrp))) {cosetOfElt x} = {!!}
