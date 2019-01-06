{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Groups
open import Naturals
open import Orders
open import Setoids
open import Functions
open import Rings

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module IntegralDomains where
  record IntegralDomain {n m : _} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) : Set (lsuc m ⊔ n) where
    field
      intDom : {a b : A} → Setoid._∼_ S (a * b) (Ring.0R R) → (Setoid._∼_ S a (Ring.0R R)) || (Setoid._∼_ S b (Ring.0R R))
      nontrivial : Setoid._∼_ S (Ring.1R R) (Ring.0R R) → False

  cancelIntDom : {m n : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} (I : IntegralDomain R) {a b c : A} → Setoid._∼_ S (a * b) (a * c) → (Setoid._∼_ S a (Ring.0R R)) || (Setoid._∼_ S b c)
  cancelIntDom {S = S} {_+_ = _+_} {_*_ = _*_} {R = R} I {a} {b} {c} ab=ac = t4
    where
      open Setoid S
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      t1 : (a * b) + Group.inverse (Ring.additiveGroup R) (a * c) ∼ Ring.0R R
      t1 = transferToRight'' (Ring.additiveGroup R) ab=ac
      t2 : a * (b + Group.inverse (Ring.additiveGroup R) c) ∼ Ring.0R R
      t2 = transitive (transitive (Ring.multDistributes R) (Group.wellDefined (Ring.additiveGroup R) reflexive (transferToRight' (Ring.additiveGroup R) (transitive (symmetric (Ring.multDistributes R)) (transitive (Ring.multWellDefined R reflexive (Group.invLeft (Ring.additiveGroup R))) (ringTimesZero R)))))) t1
      t3 : (a ∼ Ring.0R R) || ((b + Group.inverse (Ring.additiveGroup R) c) ∼ Ring.0R R)
      t3 = IntegralDomain.intDom I t2
      t4 : (a ∼ Ring.0R R) || (b ∼ c)
      t4 with t3
      ... | inl t = inl t
      ... | inr b = inr (transferToRight (Ring.additiveGroup R) b)
