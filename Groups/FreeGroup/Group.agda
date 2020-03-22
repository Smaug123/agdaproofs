{-# OPTIONS --safe --warning=error #-}

open import Setoids.Setoids
open import Groups.FreeGroup.Definition
open import Groups.Definition
open import Decidable.Sets
open import Numbers.Naturals.Order
open import LogicalFormulae
open import Semirings.Definition

module Groups.FreeGroup.Group {a : _} {A : Set a} (decA : DecidableSet A) where

open import Groups.FreeGroup.Word decA

prepend : ReducedWord → FreeCompletion A → ReducedWord
prepend empty x = prependLetter x empty (wordEmpty refl)
prepend (prependLetter (ofLetter y) w pr) (ofLetter x) = prependLetter (ofLetter x) (prependLetter (ofLetter y) w pr) (wordEnding (succIsPositive _) (freeCompletionEqualFalse decA {ofLetter x} {ofInv x} λ ()))
prepend (prependLetter (ofInv y) w pr) (ofLetter x) with DecidableSet.eq decA x y
... | inl x=y = w
... | inr x!=y = prependLetter (ofLetter x) (prependLetter (ofInv y) w pr) (wordEnding (succIsPositive _) (freeCompletionEqualFalse decA {ofLetter x} {ofLetter y} λ pr → x!=y (ofLetterInjective pr)))
prepend (prependLetter (ofLetter y) w pr) (ofInv x) with DecidableSet.eq decA x y
... | inl x=y = w
... | inr x!=y = prependLetter (ofInv x) (prependLetter (ofLetter y) w pr) (wordEnding (succIsPositive _) (freeCompletionEqualFalse decA λ pr → x!=y (ofInvInjective pr)))
prepend (prependLetter (ofInv y) w pr) (ofInv x) = prependLetter (ofInv x) (prependLetter (ofInv y) w pr) (wordEnding (succIsPositive _) (freeCompletionEqualFalse decA {ofInv x} {ofLetter x} (λ ())))

_+W_ : ReducedWord → ReducedWord → ReducedWord
empty +W b = b
prependLetter letter a x +W b = prepend (a +W b) letter

prependValid : (w : ReducedWord) (l : A) → (x : PrependIsValid w (ofLetter l)) → prepend w (ofLetter l) ≡ prependLetter (ofLetter l) w x
prependValid empty l (wordEmpty refl) = refl
prependValid (prependLetter (ofLetter l2) w x) l pr = prependLetterRefl
prependValid (prependLetter (ofInv l2) w x) l pr with DecidableSet.eq decA l l2
prependValid (prependLetter (ofInv l2) w x) .l2 (wordEnding _ x1) | inl refl = exFalso (freeCompletionEqualFalse' decA x1 refl)
... | inr l!=l2 = prependLetterRefl

prependValid' : (w : ReducedWord) (l : A) → (x : PrependIsValid w (ofInv l)) → prepend w (ofInv l) ≡ prependLetter (ofInv l) w x
prependValid' empty l (wordEmpty refl) = refl
prependValid' (prependLetter (ofLetter l2) w x) l pr with DecidableSet.eq decA l l2
prependValid' (prependLetter (ofLetter l2) w x) .l2 (wordEnding _ x1) | inl refl = exFalso (freeCompletionEqualFalse' decA x1 refl)
... | inr l!=l2 = prependLetterRefl
prependValid' (prependLetter (ofInv l2) w x) l pr = prependLetterRefl

prependInv : (w : ReducedWord) (l : A) → prepend (prepend w (ofLetter l)) (ofInv l) ≡ w
prependInv empty l with DecidableSet.eq decA l l
... | inl l=l = refl
... | inr l!=l = exFalso (l!=l refl)
prependInv (prependLetter (ofLetter l2) w x) l with DecidableSet.eq decA l l
... | inl l=l = refl
... | inr l!=l = exFalso (l!=l refl)
prependInv (prependLetter (ofInv l2) w x) l with DecidableSet.eq decA l l2
prependInv (prependLetter (ofInv l2) w x) .l2 | inl refl = prependValid' w l2 x
... | inr l!=l2 with DecidableSet.eq decA l l
prependInv (prependLetter (ofInv l2) w x) l | inr l!=l2 | inl refl = refl
prependInv (prependLetter (ofInv l2) w x) l | inr l!=l2 | inr bad = exFalso (bad refl)

prependInv' : (w : ReducedWord) (l : A) → prepend (prepend w (ofInv l)) (ofLetter l) ≡ w
prependInv' empty l with DecidableSet.eq decA l l
... | inl l=l = refl
... | inr l!=l = exFalso (l!=l refl)
prependInv' (prependLetter (ofLetter l2) w x) l with DecidableSet.eq decA l l2
prependInv' (prependLetter (ofLetter l2) w x) .l2 | inl refl = prependValid w l2 x
... | inr l!=l2 with DecidableSet.eq decA l l
... | inl refl = refl
... | inr l!=l = exFalso (l!=l refl)
prependInv' (prependLetter (ofInv l2) w x) l with DecidableSet.eq decA l l
prependInv' (prependLetter (ofInv l2) w x) l | inl refl = refl
prependInv' (prependLetter (ofInv l2) w x) l | inr l!=l = exFalso (l!=l refl)

prependAndAdd : (a b : ReducedWord) (l : FreeCompletion A) → prepend (a +W b) l ≡ (prepend a l) +W b
prependAndAdd empty b l = refl
prependAndAdd (prependLetter (ofLetter x) w pr) b (ofLetter y) = refl
prependAndAdd (prependLetter (ofLetter x) w pr) b (ofInv y) with DecidableSet.eq decA y x
prependAndAdd (prependLetter (ofLetter x) w pr) b (ofInv .x) | inl refl = prependInv _ _
... | inr y!=x = refl
prependAndAdd (prependLetter (ofInv x) w pr) b (ofLetter y) with DecidableSet.eq decA y x
prependAndAdd (prependLetter (ofInv x) w pr) b (ofLetter .x) | inl refl = prependInv' _ _
... | inr y!=x = refl
prependAndAdd (prependLetter (ofInv x) w pr) b (ofInv y) = refl

+WAssoc : (a b c : ReducedWord) → (a +W (b +W c)) ≡ ((a +W b) +W c)
+WAssoc empty b c = refl
+WAssoc (prependLetter letter a x) b c rewrite equalityCommutative (prependAndAdd (a +W b) c letter) | +WAssoc a b c = refl

inverseW : ReducedWord → ReducedWord
inverseW empty = empty
inverseW (prependLetter letter w x) = (inverseW w) +W prependLetter (freeInverse letter) empty (wordEmpty refl)

identRightW : (a : ReducedWord) → a +W empty ≡ a
identRightW empty = refl
identRightW (prependLetter (ofLetter l) a x) rewrite identRightW a = prependValid a l x
identRightW (prependLetter (ofInv l) a x) rewrite identRightW a = prependValid' a l x

invLeftW : (a : ReducedWord) → (inverseW a) +W a ≡ empty
invLeftW empty = refl
invLeftW (prependLetter (ofLetter l) a x) rewrite equalityCommutative (+WAssoc (inverseW a) (prependLetter (ofInv l) empty (wordEmpty refl)) (prependLetter (ofLetter l) a x)) = t
  where
    t : (inverseW a +W (prepend (prependLetter (ofLetter l) a x) (ofInv l))) ≡ empty
    t with DecidableSet.eq decA l l
    ... | inl refl = invLeftW a
    ... | inr l!=l = exFalso (l!=l refl)
invLeftW (prependLetter (ofInv l) a x) rewrite equalityCommutative (+WAssoc (inverseW a) (prependLetter (ofLetter l) empty (wordEmpty refl)) (prependLetter (ofInv l) a x)) = t
  where
    t : (inverseW a +W (prepend (prependLetter (ofInv l) a x) (ofLetter l))) ≡ empty
    t with DecidableSet.eq decA l l
    ... | inl refl = invLeftW a
    ... | inr l!=l = exFalso (l!=l refl)

invRightW : (a : ReducedWord) → a +W (inverseW a) ≡ empty
invRightW empty = refl
invRightW (prependLetter (ofLetter l) a x) rewrite +WAssoc a (inverseW a) (prependLetter (ofInv l) empty (wordEmpty refl)) | invRightW a = t
  where
    t : prepend (prependLetter (ofInv l) empty (wordEmpty refl)) (ofLetter l) ≡ empty
    t with DecidableSet.eq decA l l
    ... | inl refl = refl
    ... | inr l!=l = exFalso (l!=l refl)
invRightW (prependLetter (ofInv l) a x) rewrite +WAssoc a (inverseW a) (prependLetter (ofLetter l) empty (wordEmpty refl)) | invRightW a = t
  where
    t : prepend (prependLetter (ofLetter l) empty (wordEmpty refl)) (ofInv l) ≡ empty
    t with DecidableSet.eq decA l l
    ... | inl refl = refl
    ... | inr l!=l = exFalso (l!=l refl)

freeGroup : Group (reflSetoid ReducedWord) _+W_
Group.+WellDefined freeGroup refl refl = refl
Group.0G freeGroup = empty
Group.inverse freeGroup = inverseW
Group.+Associative freeGroup {a} {b} {c} = +WAssoc a b c
Group.identRight freeGroup {a} = identRightW a
Group.identLeft freeGroup {a} = refl
Group.invLeft freeGroup {a} = invLeftW a
Group.invRight freeGroup {a} = invRightW a
