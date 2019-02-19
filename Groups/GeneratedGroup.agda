{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Setoids.Lists
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Sets.FinSet
open import Groups.GroupDefinition
open import Lists
open import Orders
open import Groups.Groups

module Groups.GeneratedGroup where
  data FreeCompletion {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
    ofLetter : A → FreeCompletion S
    ofInv : A → FreeCompletion S

  freeCompletionMap : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) → FreeCompletion S → FreeCompletion T
  freeCompletionMap f (ofLetter x) = ofLetter (f x)
  freeCompletionMap f (ofInv x) = ofInv (f x)

  freeInverse : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (l : FreeCompletion S) → FreeCompletion S
  freeInverse (ofLetter x) = ofInv x
  freeInverse (ofInv x) = ofLetter x

  freeCompletionSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (FreeCompletion S)
  (freeCompletionSetoid S Setoid.∼ ofLetter w) (ofLetter x) = Setoid._∼_ S w x
  (freeCompletionSetoid S Setoid.∼ ofLetter w) (ofInv x) = False'
  (freeCompletionSetoid S Setoid.∼ ofInv w) (ofLetter x) = False'
  (freeCompletionSetoid S Setoid.∼ ofInv w) (ofInv x) = Setoid._∼_ S w x
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter x} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv x} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofLetter x} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofInv x} ()
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofLetter x} ()
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofInv x} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofLetter x} {ofLetter y} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofLetter x} {ofInv y} _ ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofInv x} {y} ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofLetter x} {y} ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofInv x} {ofLetter y} _ ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofInv x} {ofInv y} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))

  freeCompletionMapWellDefined : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) → ({x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)) → {x y : FreeCompletion S} → (Setoid._∼_ (freeCompletionSetoid S) x y) → (Setoid._∼_ (freeCompletionSetoid T) (freeCompletionMap f x) (freeCompletionMap f y))
  freeCompletionMapWellDefined f fWD {ofLetter x} {ofLetter x₁} w1=w2 = fWD w1=w2
  freeCompletionMapWellDefined f fWD {ofLetter x} {ofInv x₁} ()
  freeCompletionMapWellDefined f fWD {ofInv x} {ofLetter x₁} ()
  freeCompletionMapWellDefined f fWD {ofInv x} {ofInv x₁} w1=w2 = fWD w1=w2

  record Word {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
    field
      word : List (FreeCompletion S)

  wordSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (Word S)
  (wordSetoid S Setoid.∼ record { word = word1 }) record { word = word2 } = Setoid._∼_ (listSetoid (freeCompletionSetoid S)) word1 word2
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (wordSetoid S))) {record { word = word }} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (listSetoid (freeCompletionSetoid S))))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (wordSetoid S))) {record { word = word1 }} {record { word = word2 }} pr = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (listSetoid (freeCompletionSetoid S)))) pr
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (wordSetoid S))) {record { word = word1 }} {record { word = word2 }} {record { word = word3 }} pr1 pr2 = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (listSetoid (freeCompletionSetoid S)))) pr1 pr2

  evalWord : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) (w : Word S) → A
  evalWord G record { word = [] } = Group.identity G
  evalWord {_+_ = _+_} G record { word = (ofLetter x :: w) } = x + evalWord G record { word = w }
  evalWord {_+_ = _+_} G record { word = (ofInv x :: w) } = (Group.inverse G x) + evalWord G record { word = w }

  mapWord : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) (w : Word S) → Word T
  mapWord f record { word = word } = record { word = listMap (freeCompletionMap f) word }

  subgroupSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} (T : Setoid {b} {d} B) {_+_ : A → A → A} (G : Group S _+_) {f : B → A} (fInj : SetoidInjection T S f) → Setoid (Word T)
  Setoid._∼_ (subgroupSetoid {S = S} T G {f} fInj) w1 w2 = Setoid._∼_ S (evalWord G (mapWord f w1)) (evalWord G (mapWord f w2))
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (subgroupSetoid {S = S} T G {f} fInj))) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (subgroupSetoid {S = S} T G {f} fInj))) = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (subgroupSetoid {S = S} T G {f} fInj))) = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))

  evalWordWellDefined : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) (w1 w2 : Word S) → Setoid._∼_ (wordSetoid S) w1 w2 → Setoid._∼_ S (evalWord G w1) (evalWord G w2)
  evalWordWellDefined {S = S} G record { word = [] } record { word = [] } w1=w2 = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  evalWordWellDefined G record { word = [] } record { word = (x :: word) } ()
  evalWordWellDefined {_+_ = _+_} G record { word = (x :: xs) } record { word = [] } ()
  evalWordWellDefined {_+_ = _+_} G record { word = (ofLetter x :: xs) } record { word = (ofLetter y :: ys) } (x=y ,, snd) = Group.wellDefined G x=y (evalWordWellDefined G record { word = xs } record { word = ys } snd)
  evalWordWellDefined {_+_ = _+_} G record { word = (ofLetter x :: xs) } record { word = (ofInv y :: ys) } (() ,, snd)
  evalWordWellDefined {_+_ = _+_} G record { word = (ofInv x :: xs) } record { word = (ofLetter y :: ys) } (() ,, snd)
  evalWordWellDefined {_+_ = _+_} G record { word = (ofInv x :: xs) } record { word = (ofInv y :: ys) } (x=y ,, snd) = Group.wellDefined G (inverseWellDefined G x=y) (evalWordWellDefined G record { word = xs } record { word = ys } snd)

  mapWordWellDefined : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) → ({x y : A} → (Setoid._∼_ S x y) → (Setoid._∼_ T (f x) (f y))) → {w1 : Word S} {w2 : Word S} → Setoid._∼_ (wordSetoid S) w1 w2 → Setoid._∼_ (wordSetoid T) (mapWord f w1) (mapWord f w2)
  mapWordWellDefined {S = S} {T = T} f fWD {w1} {w2} w1=w2 = p
    where
      p : listEquality (freeCompletionSetoid T) (listMap (freeCompletionMap {S = S} {T = T} f) (Word.word w1)) (listMap (freeCompletionMap f) (Word.word w2))
      p = listEqualityRespectsMap (freeCompletionSetoid S) (freeCompletionSetoid T) (freeCompletionMap {S = S} {T} f) (λ {x} {y} → freeCompletionMapWellDefined {S = S} {T = T} f fWD {x} {y}) {w1 = Word.word w1} {w2 = Word.word w2} w1=w2

  subgroupOp : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} (T : Setoid {b} {d} B) {_+_ : A → A → A} (G : Group S _+_) {f : B → A} (fInj : SetoidInjection T S f) → Word T → Word T → Word T
  subgroupOp T G fInj record { word = word1 } record { word = word2 } = record { word = word1 ++ word2 }

  generatedSubgroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} (T : Setoid {b} {d} B) {_+_ : A → A → A} (G : Group S _+_) {f : B → A} (fInj : SetoidInjection T S f) → Group (subgroupSetoid T G fInj) (subgroupOp T G fInj)
  Group.wellDefined (generatedSubgroup {S = S} T G {f = f} fInj) {record { word = w }} {record { word = x }} {record { word = y }} {record { word = z }} w=y x=z = need
    where
      need : Setoid._∼_ (subgroupSetoid T G fInj) (subgroupOp T G fInj (record { word = w }) (record { word = x })) (subgroupOp T G fInj (record { word = y }) (record { word = z }))
      need = {!!}
  Group.identity (generatedSubgroup T G fInj) = record { word = [] }
  Group.inverse (generatedSubgroup T G fInj) record { word = word } = record { word = listMap freeInverse (listRev word) }
  Group.multAssoc (generatedSubgroup T G fInj) = {!!}
  Group.multIdentRight (generatedSubgroup {S = S} T G {f = f} fInj) {a = record { word = word }} = need
    where
      open Setoid S
      open Group G
      need : evalWord G (mapWord f (record { word = word ++ [] })) ∼ evalWord G (mapWord f record { word = word })
      need = {!!}
  Group.multIdentLeft (generatedSubgroup {S = S} T G {f = f} fInj) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Group.invLeft (generatedSubgroup {S = S} T G {f} fInj) {record { word = [] }} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Group.invLeft (generatedSubgroup {S = S} T G {f} fInj) {record { word = x :: word }} = need
    where
      open Setoid S
      open Group G
      need : Setoid._∼_ (subgroupSetoid T G fInj) (record { word = (listMap freeInverse (listRev (x :: word))) ++ (x :: word) }) (Group.identity (generatedSubgroup T G fInj))
      need = {!!}
  Group.invRight (generatedSubgroup T G fInj) = {!!}
