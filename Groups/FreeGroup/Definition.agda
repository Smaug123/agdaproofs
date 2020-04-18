{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions.Definition
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition
open import Groups.Definition
open import Groups.SymmetricGroups.Definition
open import Decidable.Sets
open import Boolean.Definition

module Groups.FreeGroup.Definition where

data FreeCompletion {a : _} (A : Set a) : Set a where
  ofLetter : A → FreeCompletion A
  ofInv : A → FreeCompletion A

freeCompletionMap : {a b : _} {A : Set a} {B : Set b} (f : A → B) (w : FreeCompletion A) → FreeCompletion B
freeCompletionMap f (ofLetter x) = ofLetter (f x)
freeCompletionMap f (ofInv x) = ofInv (f x)

freeInverse : {a : _} {A : Set a} (l : FreeCompletion A) → FreeCompletion A
freeInverse (ofLetter x) = ofInv x
freeInverse (ofInv x) = ofLetter x

ofLetterInjective : {a : _} {A : Set a} {x y : A} → (ofLetter x ≡ ofLetter y) → x ≡ y
ofLetterInjective refl = refl

ofInvInjective : {a : _} {A : Set a} {x y : A} → (ofInv x ≡ ofInv y) → x ≡ y
ofInvInjective refl = refl

ofLetterOfInv : {a : _} {A : Set a} {x y : A} → ofLetter x ≡ ofInv y → False
ofLetterOfInv ()

decidableFreeCompletion : {a : _} {A : Set a} → DecidableSet A → DecidableSet (FreeCompletion A)
decidableFreeCompletion {A = A} dec = pr
  where
    pr : (a b : FreeCompletion A) → (a ≡ b) || (a ≡ b → False)
    pr (ofLetter x) (ofLetter y) with dec x y
    ... | inl refl = inl refl
    ... | inr x!=y = inr λ p → x!=y (ofLetterInjective p)
    pr (ofLetter x) (ofInv y) = inr λ ()
    pr (ofInv x) (ofLetter y) = inr λ ()
    pr (ofInv x) (ofInv y) with dec x y
    ... | inl refl = inl refl
    ... | inr x!=y = inr λ p → x!=y (ofInvInjective p)

freeCompletionEqual : {a : _} {A : Set a} (dec : DecidableSet A) (x y : FreeCompletion A) → Bool
freeCompletionEqual dec x y with decidableFreeCompletion dec x y
freeCompletionEqual dec x y | inl x₁ = BoolTrue
freeCompletionEqual dec x y | inr x₁ = BoolFalse

freeCompletionEqualFalse : {a : _} {A : Set a} (dec : DecidableSet A) {x y : FreeCompletion A} → ((x ≡ y) → False) → (freeCompletionEqual dec x y) ≡ BoolFalse
freeCompletionEqualFalse dec {x = x} {y} x!=y with decidableFreeCompletion dec x y
freeCompletionEqualFalse dec {x} {y} x!=y | inl x=y = exFalso (x!=y x=y)
freeCompletionEqualFalse dec {x} {y} x!=y | inr _ = refl

freeCompletionEqualFalse' : {a : _} {A : Set a} (dec : DecidableSet A) {x y : FreeCompletion A} → .((freeCompletionEqual dec x y) ≡ BoolFalse) → (x ≡ y) → False
freeCompletionEqualFalse' dec {x} {y} pr with decidableFreeCompletion dec x y
freeCompletionEqualFalse' dec {x} {y} () | inl x₁
freeCompletionEqualFalse' dec {x} {y} pr | inr ans = ans

