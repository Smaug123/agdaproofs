{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.Definition
open import Numbers.Naturals.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions
open import Sets.EquivalenceRelations

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

-- Following Part IB's course Groups, Rings, and Modules, we take rings to be commutative with one.
module Rings.Definition where
  record Ring {n m} {A : Set n} (S : Setoid {n} {m} A) (_+_ : A → A → A) (_*_ : A → A → A) : Set (lsuc n ⊔ m) where
    field
      additiveGroup : Group S _+_
    open Group additiveGroup
    open Setoid S
    open Equivalence eq
    0R : A
    0R = 0G
    _-R_ : A → A → A
    a -R b = a + (inverse b)
    field
      *WellDefined : {r s t u : A} → (r ∼ t) → (s ∼ u) → r * s ∼ t * u
      1R : A
      groupIsAbelian : {a b : A} → a + b ∼ b + a
      *Associative : {a b c : A} → (a * (b * c)) ∼ (a * b) * c
      *Commutative : {a b : A} → a * b ∼ b * a
      *DistributesOver+ : {a b c : A} → a * (b + c) ∼ (a * b) + (a * c)
      identIsIdent : {a : A} → 1R * a ∼ a
    timesZero : {a : A} → a * 0R ∼ 0R
    timesZero {a} = symmetric (transitive (transitive (symmetric invLeft) (+WellDefined reflexive (transitive (*WellDefined {a} {a} reflexive (symmetric identRight)) *DistributesOver+))) (transitive +Associative (transitive (+WellDefined invLeft reflexive) identLeft)))


  --directSumRing : {m n : _} → {A : Set m} {B : Set n} (r : Ring A) (s : Ring B) → Ring (A && B)
  --Ring.additiveGroup (directSumRing r s) = directSumGroup (Ring.additiveGroup r) (Ring.additiveGroup s)
  --Ring._*_ (directSumRing r s) (a ,, b) (c ,, d) = (Ring._*_ r a c) ,, Ring._*_ s b d
  --Ring.multWellDefined (directSumRing r s) (a ,, b) (c ,, d) = Ring.multWellDefined r a c ,, Ring.multWellDefined s b d
  --Ring.1R (directSumRing r s) = Ring.1R r ,, Ring.1R s
  --Ring.groupIsAbelian (directSumRing r s) = Ring.groupIsAbelian r ,, Ring.groupIsAbelian s
  --Ring.assoc (directSumRing r s) = Ring.assoc r ,, Ring.assoc s
  --Ring.multCommutative (directSumRing r s) = Ring.multCommutative r ,, Ring.multCommutative s
  --Ring.multDistributes (directSumRing r s) = Ring.multDistributes r ,, Ring.multDistributes s
  --Ring.identIsIdent (directSumRing r s) = Ring.identIsIdent r ,, Ring.identIsIdent s

  record RingHom {m n o p : _} {A : Set m} {B : Set n} {SA : Setoid {m} {o} A} {SB : Setoid {n} {p} B} {_+A_ : A → A → A} {_*A_ : A → A → A} (R : Ring SA _+A_ _*A_) {_+B_ : B → B → B} {_*B_ : B → B → B} (S : Ring SB _+B_ _*B_) (f : A → B) : Set (m ⊔ n ⊔ o ⊔ p) where
    open Ring S
    open Group additiveGroup
    open Setoid SB
    field
      preserves1 : f (Ring.1R R) ∼ 1R
      ringHom : {r s : A} → f (r *A s) ∼ (f r) *B (f s)
      groupHom : GroupHom (Ring.additiveGroup R) additiveGroup f

  --record RingIso {m n : _} {A : Set m} {B : Set n} (R : Ring A) (S : Ring B) (f : A → B) : Set (m ⊔ n) where
  --  field
  --    ringHom : RingHom R S f
  --    bijective : Bijection f
