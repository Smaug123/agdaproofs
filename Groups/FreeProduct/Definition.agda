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
