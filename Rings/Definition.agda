{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Groups.Groups
open import Groups.GroupDefinition
open import Numbers.Naturals
open import Setoids.Orders
open import Setoids.Setoids
open import Functions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

-- Following Part IB's course Groups, Rings, and Modules, we take rings to be commutative with one.
module Rings.Definition where
  record Ring {n m} {A : Set n} (S : Setoid {n} {m} A) (_+_ : A → A → A) (_*_ : A → A → A) : Set (lsuc n ⊔ m) where
    field
      additiveGroup : Group S _+_
    open Group additiveGroup
    open Setoid S
    0R : A
    0R = identity
    field
      multWellDefined : {r s t u : A} → (r ∼ t) → (s ∼ u) → r * s ∼ t * u
      1R : A
      groupIsAbelian : {a b : A} → a + b ∼ b + a
      multAssoc : {a b c : A} → (a * (b * c)) ∼ (a * b) * c
      multCommutative : {a b : A} → a * b ∼ b * a
      multDistributes : {a b c : A} → a * (b + c) ∼ (a * b) + (a * c)
      multIdentIsIdent : {a : A} → 1R * a ∼ a

  record OrderedRing {n m p} {A : Set n} {S : Setoid {n} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} (R : Ring S _+_ _*_) (order : SetoidTotalOrder pOrder) : Set (lsuc n ⊔ m ⊔ p) where
    open Ring R
    open Group additiveGroup
    open Setoid S
    field
      orderRespectsAddition : {a b : A} → (a < b) → (c : A) → (a + c) < (b + c)
      orderRespectsMultiplication : {a b : A} → (0R < a) → (0R < b) → (0R < (a * b))

  --directSumRing : {m n : _} → {A : Set m} {B : Set n} (r : Ring A) (s : Ring B) → Ring (A && B)
  --Ring.additiveGroup (directSumRing r s) = directSumGroup (Ring.additiveGroup r) (Ring.additiveGroup s)
  --Ring._*_ (directSumRing r s) (a ,, b) (c ,, d) = (Ring._*_ r a c) ,, Ring._*_ s b d
  --Ring.multWellDefined (directSumRing r s) (a ,, b) (c ,, d) = Ring.multWellDefined r a c ,, Ring.multWellDefined s b d
  --Ring.1R (directSumRing r s) = Ring.1R r ,, Ring.1R s
  --Ring.groupIsAbelian (directSumRing r s) = Ring.groupIsAbelian r ,, Ring.groupIsAbelian s
  --Ring.multAssoc (directSumRing r s) = Ring.multAssoc r ,, Ring.multAssoc s
  --Ring.multCommutative (directSumRing r s) = Ring.multCommutative r ,, Ring.multCommutative s
  --Ring.multDistributes (directSumRing r s) = Ring.multDistributes r ,, Ring.multDistributes s
  --Ring.multIdentIsIdent (directSumRing r s) = Ring.multIdentIsIdent r ,, Ring.multIdentIsIdent s

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


  abs : {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {c} A} {pOrder : SetoidPartialOrder S _<_} (R : Ring S _+_ _*_) (order : SetoidTotalOrder pOrder) (x : A) → A
  abs R order x with SetoidTotalOrder.totality order (Ring.0R R) x
  ... | inl (inl 0<x) = x
  ... | inl (inr x<0) = Group.inverse (Ring.additiveGroup R) x
  ... | inr 0=x = Ring.0R R
