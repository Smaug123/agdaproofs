{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Setoids.Setoids
open import Groups.Definition
open import LogicalFormulae
open import Orders.WellFounded.Definition
open import Numbers.Naturals.Semiring
open import Groups.Lemmas

module Groups.FreeProduct.Group {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) {a b : _} {A : I → Set a} {S : (i : I) → Setoid {a} {b} (A i)} {_+_ : (i : I) → (A i) → (A i) → A i} (decidableGroups : (i : I) → (x y : A i) → ((Setoid._∼_ (S i) x y)) || ((Setoid._∼_ (S i) x y) → False)) (G : (i : I) → Group (S i) (_+_ i)) where

open import Groups.FreeProduct.Definition decidableIndex decidableGroups G
open import Groups.FreeProduct.Setoid decidableIndex decidableGroups G
open import Groups.FreeProduct.Addition decidableIndex decidableGroups G

private
  inv' : {i : I} (x : ReducedSequenceBeginningWith i) → Sg I (λ j → ReducedSequenceBeginningWith j)
  inv' (ofEmpty i g nonZero) = i , ofEmpty i (Group.inverse (G i) g) (λ pr → nonZero (Equivalence.transitive (Setoid.eq (S i)) (swapInv (G i) pr) (invIdent (G i))))
  inv' (prependLetter i g nonZero x x₁) with inv' x
  inv' (prependLetter i g nonZero x x₁) | j , xInv with plus' xInv (injection (Group.inverse (G i) g) (λ pr → nonZero (Equivalence.transitive (Setoid.eq (S i)) (swapInv (G i) pr) (invIdent (G i)))))
  inv' (prependLetter i g nonZero x x₁) | j , xInv | empty = _ , x -- this case actually can't happen but I can't be bothered to prove it
  inv' (prependLetter i g nonZero x x₁) | j , xInv | nonempty k ans = k , ans

  inv : (x : ReducedSequence) → ReducedSequence
  inv empty = empty
  inv (nonempty i w) with inv' w
  ... | a , b = nonempty a b

invRight : (a : ReducedSequence) → (a +RP (inv a)) =RP empty
invRight empty = record {}
invRight (nonempty i x) with inv' x
invRight (nonempty i (ofEmpty .i g nonZero)) | a , b with decidableIndex i a
invRight (nonempty i (ofEmpty .i g nonZero)) | .i , ofEmpty .i h nonZeroH | inl refl with decidableGroups i ((i + g) h) (Group.0G (G i))
invRight (nonempty i (ofEmpty .i g nonZero)) | .i , ofEmpty .i h nonZeroH | inl refl | inl x = record {}
invRight (nonempty i (ofEmpty .i g nonZero)) | .i , ofEmpty .i h nonZeroH | inl refl | inr x = {!!}
invRight (nonempty i (ofEmpty .i g nonZero)) | .i , prependLetter .i h nonZeroH b x | inl refl with decidableGroups i ((i + g) h) (Group.0G (G i))
invRight (nonempty i (ofEmpty .i g nonZero)) | .i , prependLetter .i h nonZeroH {j} b x | inl refl | inl x₁ = {!!}
invRight (nonempty i (ofEmpty .i g nonZero)) | .i , prependLetter .i h nonZeroH b x | inl refl | inr x₁ = {!!}
invRight (nonempty i (ofEmpty .i g nonZero)) | a , b | inr x = {!!}
invRight (nonempty i (prependLetter .i g nonZero x x₁)) | a , b = {!!}

FreeProductGroup : Group freeProductSetoid _+RP_
Group.+WellDefined FreeProductGroup {m} {n} {x} {y} m=x n=y = plusWD m n x y m=x n=y
Group.0G FreeProductGroup = empty
Group.inverse FreeProductGroup = inv
Group.+Associative FreeProductGroup = {!!}
Group.identRight FreeProductGroup {empty} = Equivalence.reflexive (Setoid.eq freeProductSetoid) {empty}
Group.identRight FreeProductGroup {nonempty i x} = {!!}
Group.identLeft FreeProductGroup {empty} = Equivalence.reflexive (Setoid.eq freeProductSetoid) {empty}
Group.identLeft FreeProductGroup {nonempty i x} = Equivalence.reflexive (Setoid.eq freeProductSetoid) {nonempty i x}
Group.invLeft FreeProductGroup = {!!}
Group.invRight FreeProductGroup = {!!}
