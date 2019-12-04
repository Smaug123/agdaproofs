{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Decidable.Relations where

DecidableRelation : {a b : _} {A : Set a} (f : A → Set b) → Set (a ⊔ b)
DecidableRelation {A = A} f = (x : A) → (f x) || (f x → False)

orDecidable : {a b c : _} {A : Set a} {f : A → Set b} {g : A → Set c} → DecidableRelation f → DecidableRelation g → DecidableRelation (λ x → (f x) || (g x))
orDecidable fDec gDec x with fDec x
orDecidable fDec gDec x | inl fx = inl (inl fx)
orDecidable fDec gDec x | inr !fx with gDec x
orDecidable fDec gDec x | inr !fx | inl gx = inl (inr gx)
orDecidable {f = f} {g} fDec gDec x | inr !fx | inr !gx = inr t
  where
    t : (f x || g x) → False
    t (inl x) = !fx x
    t (inr x) = !gx x

andDecidable : {a b c : _} {A : Set a} {f : A → Set b} {g : A → Set c} → DecidableRelation f → DecidableRelation g → DecidableRelation (λ x → (f x) && (g x))
andDecidable fDec gDec x with fDec x
andDecidable fDec gDec x | inl fx with gDec x
andDecidable fDec gDec x | inl fx | inl gx = inl (fx ,, gx)
andDecidable fDec gDec x | inl fx | inr !gx = inr (λ x → !gx (_&&_.snd x))
andDecidable fDec gDec x | inr !fx = inr (λ x → !fx (_&&_.fst x))

notDecidable : {a b : _} {A : Set a} {f : A → Set b} → DecidableRelation f → DecidableRelation (λ x → (f x) → False)
notDecidable fDec x with fDec x
notDecidable fDec x | inl fx = inr (λ x → x fx)
notDecidable fDec x | inr !fx = inl !fx

doubleNegation : {a b : _} {A : Set a} {f : A → Set b} → DecidableRelation f → (x : A) → (((f x) → False) → False) → f x
doubleNegation fDec x with fDec x
doubleNegation fDec x | inl fx = λ _ → fx
doubleNegation fDec x | inr !fx = λ p → exFalso (p !fx)
