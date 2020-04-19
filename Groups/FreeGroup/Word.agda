{-# OPTIONS --safe --warning=error #-}

open import Setoids.Setoids
open import Groups.SymmetricGroups.Definition
open import Groups.FreeGroup.Definition
open import Decidable.Sets
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Boolean.Definition

module Groups.FreeGroup.Word {a : _} {A : Set a} (decA : DecidableSet A) where

data ReducedWord : Set a
wordLength : ReducedWord → ℕ
firstLetter : (w : ReducedWord) → .(0 <N wordLength w) → FreeCompletion A

data PrependIsValid (w : ReducedWord) (l : FreeCompletion A) : Set a where
  wordEmpty : wordLength w ≡ 0 → PrependIsValid w l
  wordEnding : .(pr : 0 <N wordLength w) → .(freeCompletionEqual decA l (freeInverse (firstLetter w pr)) ≡ BoolFalse) → PrependIsValid w l

data ReducedWord where
  empty : ReducedWord
  prependLetter : (letter : FreeCompletion A) → (w : ReducedWord) → PrependIsValid w letter → ReducedWord

firstLetter empty ()
firstLetter (prependLetter letter w x) pr = letter

wordLength empty = 0
wordLength (prependLetter letter w pr) = succ (wordLength w)

prependLetterRefl : {x : FreeCompletion A} {w : ReducedWord} → {pr1 pr2 : PrependIsValid w x} → prependLetter x w pr1 ≡ prependLetter x w pr2
prependLetterRefl {x} {empty} {wordEmpty refl} {wordEmpty refl} = refl
prependLetterRefl {x} {empty} {wordEmpty refl} {wordEnding () x₂}
prependLetterRefl {x} {empty} {wordEnding () x₁} {pr2}
prependLetterRefl {x} {prependLetter letter w x₁} {wordEmpty ()} {pr2}
prependLetterRefl {x} {prependLetter letter w x₁} {wordEnding pr x₂} {wordEmpty ()}
prependLetterRefl {x} {prependLetter letter w x₁} {wordEnding pr2 r2} {wordEnding pr1 r1} = refl

prependLetterInjective : {x : FreeCompletion A} {w1 w2 : ReducedWord} {pr1 : PrependIsValid w1 x} {pr2 : PrependIsValid w2 x} → prependLetter x w1 pr1 ≡ prependLetter x w2 pr2 → w1 ≡ w2
prependLetterInjective {x = x} {empty} {empty} {pr1} {pr2} pr = refl
prependLetterInjective {x = x} {prependLetter l1 w1 x1} {prependLetter .l1 .w1 .x1} {wordEnding pr₁ x₁} {wordEnding pr₂ x₂} refl = refl

prependLetterInjective' : {x y : FreeCompletion A} {w1 w2 : ReducedWord} {pr1 : PrependIsValid w1 x} {pr2 : PrependIsValid w2 y} → prependLetter x w1 pr1 ≡ prependLetter y w2 pr2 → x ≡ y
prependLetterInjective' refl = refl

badPrepend : {x : A} {w : ReducedWord} {pr : PrependIsValid w (ofInv x)} → (PrependIsValid (prependLetter (ofInv x) w pr) (ofLetter x)) → False
badPrepend (wordEmpty ())
badPrepend {x = x} (wordEnding pr bad) with decidableFreeCompletion decA (ofLetter x) (ofLetter x)
badPrepend {x} (wordEnding pr ()) | inl x₁
badPrepend {x} (wordEnding pr bad) | inr pr2 = pr2 refl

badPrepend' : {x : A} {w : ReducedWord} {pr : PrependIsValid w (ofLetter x)} → (PrependIsValid (prependLetter (ofLetter x) w pr) (ofInv x)) → False
badPrepend' (wordEmpty ())
badPrepend' {x = x} (wordEnding pr x₁) with decidableFreeCompletion decA (ofInv x) (ofInv x)
badPrepend' {x} (wordEnding pr ()) | inl x₂
badPrepend' {x} (wordEnding pr x₁) | inr pr2 = pr2 refl
