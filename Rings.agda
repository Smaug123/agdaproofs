{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Groups
open import Naturals
open import Orders
open import Setoids
open import Functions

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

-- Following Part IB's course Groups, Rings, and Modules, we take rings to be commutative with one.
module Rings where
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

  record OrderedRing {n m o} {A : Set n} (S : Setoid {n} {m} A) (_+_ : A → A → A) (_*_ : A → A → A) : Set (lsuc n ⊔ m ⊔ lsuc o) where
    field
      ring : Ring S _+_ _*_
    open Ring ring
    open Group additiveGroup
    open Setoid S
    field
      order : TotalOrder {_} {o} A
    _<_ = TotalOrder._<_ order
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

  ringTimesZero : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} (R : Ring S _+_ _*_) → {x : A} → Setoid._∼_ S (x * (Ring.0R R)) (Ring.0R R)
  ringTimesZero {S = S} {_+_ = _+_} {_*_ = _*_} R {x} = symmetric (transitive blah'' (transitive (Group.multAssoc additiveGroup) (transitive (wellDefined invLeft reflexive) multIdentLeft)))
    where
      open Ring R
      open Group additiveGroup
      open Setoid S
      open Transitive (Equivalence.transitiveEq (Setoid.eq S))
      open Reflexive (Equivalence.reflexiveEq (Setoid.eq S))
      open Symmetric (Equivalence.symmetricEq (Setoid.eq S))
      blah : (x * 0R) ∼ (x * 0R) + (x * 0R)
      blah = transitive (multWellDefined reflexive (symmetric multIdentRight)) multDistributes
      blah' : (inverse (x * 0R)) + (x * 0R) ∼ (inverse (x * 0R)) + ((x * 0R) + (x * 0R))
      blah' = wellDefined reflexive blah
      blah'' : 0R ∼ (inverse (x * 0R)) + ((x * 0R) + (x * 0R))
      blah'' = transitive (symmetric invLeft) blah'
