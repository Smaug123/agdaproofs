{-# OPTIONS --warning=error --without-K --guardedness --safe #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition
open import Setoids.Setoids

module Sequences where

record Sequence {a : _} (A : Set a) : Set a where
  coinductive
  field
    head : A
    tail : Sequence A

constSequence : {a : _} {A : Set a} (k : A) → Sequence A
Sequence.head (constSequence k) = k
Sequence.tail (constSequence k) = constSequence k

index : {a : _} {A : Set a} (s : Sequence A) (n : ℕ) → A
index s zero = Sequence.head s
index s (succ n) = index (Sequence.tail s) n

funcToSequence : {a : _} {A : Set a} (f : ℕ → A) → Sequence A
Sequence.head (funcToSequence f) = f 0
Sequence.tail (funcToSequence f) = funcToSequence (λ i → f (succ i))

funcToSequenceReversible : {a : _} {A : Set a} (f : ℕ → A) → (n : ℕ) → index (funcToSequence f) n ≡ f n
funcToSequenceReversible f zero = refl
funcToSequenceReversible f (succ n) = funcToSequenceReversible (λ i → f (succ i)) n

map : {a b : _} {A : Set a} {B : Set b} (f : A → B) (s : Sequence A) → Sequence B
Sequence.head (map f s) = f (Sequence.head s)
Sequence.tail (map f s) = map f (Sequence.tail s)

apply : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) (s1 : Sequence A) (s2 : Sequence B) → Sequence C
Sequence.head (apply f s1 s2) = f (Sequence.head s1) (Sequence.head s2)
Sequence.tail (apply f s1 s2) = apply f (Sequence.tail s1) (Sequence.tail s2)

indexAndConst : {a : _} {A : Set a} (a : A) (n : ℕ) → index (constSequence a) n ≡ a
indexAndConst a zero = refl
indexAndConst a (succ n) = indexAndConst a n

mapTwice : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (f : A → B) (g : B → C) (s : Sequence A) → {n : ℕ} → index (map g (map f s)) n ≡ index (map (λ i → g (f i)) s) n
mapTwice f g s {zero} = refl
mapTwice f g s {succ n} = mapTwice f g (Sequence.tail s) {n}

mapAndIndex : {a b : _} {A : Set a} {B : Set b} (s : Sequence A) (f : A → B) (n : ℕ) → f (index s n) ≡ index (map f s) n
mapAndIndex s f zero = refl
mapAndIndex s f (succ n) = mapAndIndex (Sequence.tail s) f n

indexExtensional : {a b c : _} {A : Set a} {B : Set b} (T : Setoid {_} {c} B) (s : Sequence A) (f g : A → B) → (extension : ∀ {x} → (Setoid._∼_ T (f x) (g x))) → {n : ℕ} → Setoid._∼_ T (index (map f s) n) (index (map g s) n)
indexExtensional T s f g extension {zero} = extension
indexExtensional T s f g extension {succ n} = indexExtensional T (Sequence.tail s) f g extension {n}

indexAndApply : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (s1 : Sequence A) (s2 : Sequence B) (f : A → B → C) → {m : ℕ} → index (apply f s1 s2) m ≡ f (index s1 m) (index s2 m)
indexAndApply s1 s2 f {zero} = refl
indexAndApply s1 s2 f {succ m} = indexAndApply (Sequence.tail s1) (Sequence.tail s2) f {m}

mapAndApply : {a b c d : _} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (s1 : Sequence A) (s2 : Sequence B) (f : A → B → C) (g : C → D) → (m : ℕ) → index (map g (apply f s1 s2)) m ≡ g (f (index s1 m) (index s2 m))
mapAndApply s1 s2 f g zero = refl
mapAndApply s1 s2 f g (succ m) = mapAndApply (Sequence.tail s1) (Sequence.tail s2) f g m
