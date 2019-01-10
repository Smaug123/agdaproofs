{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Naturals
open import FinSet
open import Groups

module FreeGroups where
  data FreeCompletion {a : _} (A : Set a) : Set a where
    letter : A → FreeCompletion A
    inv : A → FreeCompletion A

  data FreeGroup {a : _} (A : Set a) : Set a where
    emptyWord : FreeGroup A
    append : FreeCompletion A → FreeGroup A → FreeGroup A

  reduceWord : {a : _} {A : Set a} → (FreeGroup {a} A) → FreeGroup A
  reduceWord emptyWord = emptyWord
  reduceWord (append (letter x) emptyWord) = append (letter x) emptyWord
  reduceWord (append (letter x) (append (letter x1) w)) = append (letter x) (reduceWord (append (letter x1) w))
  reduceWord (append (letter x) (append (inv x₁) w)) = {!!}
  reduceWord (append (inv x) w) = {!!}

  freeGroupSetoid : {a : _} (A : Set a) → Setoid A
  Setoid._∼_ (freeGroupSetoid A) = {!!}
  Setoid.eq (freeGroupSetoid A) = {!!}

  freeGroup : {a : _} (A : Set a) → Group (freeGroupSetoid A) {!!}
  freeGroup A = {!!}
