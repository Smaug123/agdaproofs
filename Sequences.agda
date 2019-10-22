{-# OPTIONS --warning=error --without-K --guardedness --safe #-}

open import LogicalFormulae
open import Numbers.Naturals.Definition

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

apply : {a b c : _} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) (s1 : Sequence A) (s2 : Sequence B) → Sequence C
Sequence.head (apply f s1 s2) = f (Sequence.head s1) (Sequence.head s2)
Sequence.tail (apply f s1 s2) = apply f (Sequence.tail s1) (Sequence.tail s2)

indexAndConst : {a : _} {A : Set a} (a : A) (n : ℕ) → index (constSequence a) n ≡ a
indexAndConst a zero = refl
indexAndConst a (succ n) = indexAndConst a n
