{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations
open import Groups.Abelian.Definition

module Groups.Abelian.DirectSum {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} {_+1_ : A → A → A} {_+2_ : B → B → B} {G1' : Group S _+1_} {G2' : Group T _+2_} (G1 : AbelianGroup G1') (G2 : AbelianGroup G2') where

open import Groups.DirectSum.Definition G1' G2'
open import Setoids.DirectSum S T

directSumAbGroup : AbelianGroup directSumGroup
AbelianGroup.commutative directSumAbGroup = directSumLift (AbelianGroup.commutative G1) (AbelianGroup.commutative G2)
