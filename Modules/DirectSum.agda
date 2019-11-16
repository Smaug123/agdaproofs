{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Homomorphisms.Definition
open import Groups.Definition
open import Groups.Abelian.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Modules.Definition

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Modules.DirectSum {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+R_ : A → A → A} {_*R_ : A → A → A} (R : Ring S _+R_ _*R_) {m n o p : _} {M : Set m} {T : Setoid {m} {n} M} {_+_ : M → M → M} {G' : Group T _+_} {G : AbelianGroup G'} {_·1_ : A → M → M} {N : Set o} {U : Setoid {o} {p} N} {_+'_ : N → N → N} {H' : Group U _+'_} {H : AbelianGroup H'} {_·2_ : A → N → N} (M1 : Module R G _·1_) (M2 : Module R H _·2_) where

open import Groups.Abelian.DirectSum G H
open import Setoids.DirectSum T U

directSumModule : Module R directSumAbGroup λ r mn → ((r ·1 (_&&_.fst mn)) ,, (r ·2 (_&&_.snd mn)))
Module.dotWellDefined directSumModule r=s t=u = directSumLift (Module.dotWellDefined M1 r=s (_&&_.fst t=u)) (Module.dotWellDefined M2 r=s (_&&_.snd t=u))
Module.dotDistributesLeft directSumModule = directSumLift (Module.dotDistributesLeft M1) (Module.dotDistributesLeft M2)
Module.dotDistributesRight directSumModule = directSumLift (Module.dotDistributesRight M1) (Module.dotDistributesRight M2)
Module.dotAssociative directSumModule = directSumLift (Module.dotAssociative M1) (Module.dotAssociative M2)
Module.dotIdentity directSumModule = directSumLift (Module.dotIdentity M1) (Module.dotIdentity M2)
