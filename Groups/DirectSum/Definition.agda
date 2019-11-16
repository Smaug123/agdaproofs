{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Groups.Definition
open import Sets.EquivalenceRelations

module Groups.DirectSum.Definition {m n o p : _} {A : Set m} {S : Setoid {m} {o} A} {_·A_ : A → A → A} {B : Set n} {T : Setoid {n} {p} B} {_·B_ : B → B → B} (G : Group S _·A_) (H : Group T _·B_) where

open import Setoids.DirectSum S T

directSumGroup : Group directSumSetoid (λ x1 y1 → (((_&&_.fst x1) ·A (_&&_.fst y1)) ,, ((_&&_.snd x1) ·B (_&&_.snd y1))))
Group.+WellDefined directSumGroup (s ,, t) (u ,, v) = Group.+WellDefined G s u ,, Group.+WellDefined H t v
Group.0G directSumGroup = (Group.0G G ,, Group.0G H)
Group.inverse directSumGroup (g1 ,, H1) = (Group.inverse G g1) ,, (Group.inverse H H1)
Group.+Associative directSumGroup = Group.+Associative G ,, Group.+Associative H
Group.identRight directSumGroup = Group.identRight G ,, Group.identRight H
Group.identLeft directSumGroup = Group.identLeft G ,, Group.identLeft H
Group.invLeft directSumGroup = Group.invLeft G ,, Group.invLeft H
Group.invRight directSumGroup = Group.invRight G ,, Group.invRight H
