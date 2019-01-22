{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Sets.FinSet
open import Groups.GroupDefinition

module Groups.FreeGroups where
  data FreeCompletion {a : _} (A : Set a) : Set a where
    letter : A → FreeCompletion A
    inv : A → FreeCompletion A

  freeInverse : {a : _} {A : Set a} (l : FreeCompletion A) → FreeCompletion A
  freeInverse (letter x) = inv x
  freeInverse (inv x) = letter x

  data ReducedWord {a : _} (A : Set a) : Set a
  wordLength : {a : _} {A : Set a} → ReducedWord A → ℕ
  lastLetter : {a : _} {A : Set a} → (w : ReducedWord A) → (0 <N wordLength w) → FreeCompletion A

  data AppendIsValid {a : _} {A : Set a} (w : ReducedWord A) (l : FreeCompletion A) : Set a where
    wordEmpty : wordLength w ≡ 0 → AppendIsValid w l
    wordEnding : (pr : 0 <N wordLength w) → ((l ≡ freeInverse (lastLetter w pr)) → False) → AppendIsValid w l

  data ReducedWord {a} A where
    empty : ReducedWord A
    addLetter : (letter : FreeCompletion A) → (w : ReducedWord A) → AppendIsValid w letter → ReducedWord A

  lastLetter {a} {A} empty ()
  lastLetter {a} {A} (addLetter letter₁ w x) _ with inspect (wordLength w)
  lastLetter {a} {A} (addLetter l w x) pr | zero with≡ _ = l
  lastLetter {a} {A} (addLetter letter₁ w x) _ | succ len with≡ p = lastLetter w (identityOfIndiscernablesRight _ _ _ _<N_ (succIsPositive len) (equalityCommutative p))

  wordLength {a} {A} empty = 0
  wordLength {a} {A} (addLetter letter₁ w pr) = succ (wordLength w)
