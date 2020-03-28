{-# OPTIONS --safe --warning=error --without-K #-}

open import Sets.EquivalenceRelations
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Setoids.Setoids
open import Groups.Definition
open import LogicalFormulae
open import Orders.WellFounded.Definition
open import Numbers.Naturals.Semiring
open import Groups.Lemmas

module Groups.FreeProduct.Definition {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) {a b : _} {A : I → Set a} {S : (i : I) → Setoid {a} {b} (A i)} {_+_ : (i : I) → (A i) → (A i) → A i} (decidableGroups : (i : I) → (x y : A i) → ((Setoid._∼_ (S i) x y)) || ((Setoid._∼_ (S i) x y) → False)) (G : (i : I) → Group (S i) (_+_ i)) where

data ReducedSequenceBeginningWith : I → Set (a ⊔ b ⊔ i) where
  ofEmpty : (i : I) → (g : A i) → .(nonZero : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → ReducedSequenceBeginningWith i
  prependLetter : (i : I) → (g : A i) → .(nonZero : Setoid._∼_ (S i) g (Group.0G (G i)) → False) → {j : I} → ReducedSequenceBeginningWith j → ((i ≡ j) → False) → ReducedSequenceBeginningWith i

data ReducedSequence : Set (a ⊔ b ⊔ i) where
  empty : ReducedSequence
  nonempty : (i : I) → ReducedSequenceBeginningWith i → ReducedSequence

injection : {i : I} (x : A i) .(nonzero : (Setoid._∼_ (S i) x (Group.0G (G i))) → False) → ReducedSequence
injection {i} x nonzero = nonempty i (ofEmpty i x nonzero)

length' : {k : _} → ReducedSequenceBeginningWith k → ℕ
length' (ofEmpty i g nonZero) = 1
length' (prependLetter i g nonZero x x₁) = succ (length' x)

length : ReducedSequence → ℕ
length empty = 0
length (nonempty i x) = length' x

{-
plus'Length : {j : _} (w : ReducedSequenceBeginningWith j) → {k : _} (x : A k) → (nonzero : (Setoid._∼_ (S k) x (Group.0G (G k))) → False) → (length (plus' w (injection x nonzero)) ≡ length' w) || ((length (plus' w (injection x nonzero)) ≡ succ (length' w)) || (succ (length (plus' w (injection x nonzero))) ≡ length' w))
plus'Length (ofEmpty i g nonZero) {k} nonzero x with decidableIndex i k
plus'Length (ofEmpty i g nonZero) {.i} nonzero y | inl refl with decidableGroups i ((i + g) nonzero) (Group.0G (G i))
plus'Length (ofEmpty i g nonZero) {.i} nonzero y | inl refl | inl x = inr (inr refl)
plus'Length (ofEmpty i g nonZero) {.i} nonzero y | inl refl | inr x = inl refl
plus'Length (ofEmpty i g nonZero) {k} nonzero y | inr pr = inr (inl refl)
plus'Length (prependLetter i g nonZero w pr) {k} nonzero x with plus'Length w g nonZero
plus'Length (prependLetter i g nonZero w pr) {k} nonzero x | inl p1 = {!!}
plus'Length (prependLetter i g nonZero w pr) {k} nonzero x | inr (inl p1) = inr (inl {!!})
plus'Length (prependLetter i g nonZero w pr) {k} nonzero x | inr (inr p1) = inr (inr {!!})

{-
plus'Length (prependLetter i g nonZero (ofEmpty j g₁ nonZero₁) x₁) {k} nonzero x with decidableIndex j k
plus'Length (prependLetter i g nonZero (ofEmpty j h nonZero₁) x₁) {.j} nonzero pr | inl refl with decidableGroups j ((j + h) nonzero) (Group.0G (G j))
plus'Length (prependLetter i g nonZero (ofEmpty j h nonZero₁) x₁) {.j} nonzero pr | inl refl | inl x = inr (inr refl)
plus'Length (prependLetter i g nonZero (ofEmpty j h nonZero₁) x₁) {.j} nonzero pr | inl refl | inr x with decidableIndex i j
plus'Length (prependLetter .j g nonZero (ofEmpty j h nonZero₁) x₁) {.j} nonzero pr | inl refl | inr jhNonzero | inl refl with decidableGroups j ((j + g) ((j + h) nonzero)) (Group.0G (G j))
plus'Length (prependLetter .j g nonZero (ofEmpty j h nonZero₁) pr2) {.j} nonzero pr | inl refl | inr jhNonzero | inl refl | inl j+g=j+h = exFalso (pr2 refl)
plus'Length (prependLetter .j g nonZero (ofEmpty j h nonZero₁) x₁) {.j} nonzero pr | inl refl | inr jhNonzero | inl refl | inr x = inr (inr refl)
plus'Length (prependLetter i g nonZero (ofEmpty j h nonZero₁) x₁) {.j} nonzero pr | inl refl | inr jhNonzero | inr x = inl refl
plus'Length (prependLetter i g nonZero (ofEmpty j g₁ nonZero₁) x₁) {k} nonzero pr | inr b with decidableIndex i j
plus'Length (prependLetter .j g nonZero (ofEmpty j h nonZero₁) x₁) {k} nonzero pr | inr b | inl refl with decidableGroups j ((j + g) h) (Group.0G (G j))
plus'Length (prependLetter .j g nonZero (ofEmpty j h nonZero₁) x₁) {k} nonzero pr | inr b | inl refl | inl x = inr (inr refl)
plus'Length (prependLetter .j g nonZero (ofEmpty j h nonZero₁) x₁) {k} nonzero pr | inr b | inl refl | inr x = inl refl
plus'Length (prependLetter i g nonZero (ofEmpty j g₁ nonZero₁) x₁) {k} nonzero pr | inr b | inr x = inr (inl refl)
plus'Length (prependLetter i g nonZero (prependLetter i₁ g₁ nonZero₁ w x₂) x₁) nonzero x = {!!}
-}

-}
