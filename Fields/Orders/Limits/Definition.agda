{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Setoids.Subset
open import Setoids.Setoids
open import Setoids.Orders
open import Sets.EquivalenceRelations
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Rings.Definition
open import Fields.Fields
open import Groups.Definition
open import Sequences
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Semirings.Definition
open import Functions
open import Fields.Orders.Total.Definition

module Fields.Orders.Limits.Definition {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {c} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {F : Field R} {pRing : PartiallyOrderedRing R pOrder} (oF : TotallyOrderedField F pRing) where

open Ring R
open TotallyOrderedField oF
open TotallyOrderedRing oRing
open PartiallyOrderedRing pRing
open import Rings.Orders.Total.Lemmas oRing
open import Rings.Orders.Partial.Lemmas pRing
open SetoidTotalOrder total
open SetoidPartialOrder pOrder
open Group additiveGroup
open import Groups.Lemmas additiveGroup
open Setoid S
open Equivalence eq
open Field F
open import Fields.CauchyCompletion.Definition (TotallyOrderedField.oRing oF) F

_~>_ : Sequence A → A → Set (a ⊔ c)
x ~> c = (ε : A) → (0R < ε) → Sg ℕ (λ N → (n : ℕ) → (N <N n) → abs ((index x n) + inverse c) < ε)

1/2 : A
1/2 with allInvertible (1R + 1R) (orderedImpliesCharNot2 nontrivial)
... | a , _ = a

abstract
  1/2is1/2 : (1/2 * (1R + 1R)) ∼ 1R
  1/2is1/2 with allInvertible (1R + 1R) (orderedImpliesCharNot2 nontrivial)
  ... | a , pr = pr

  0<1/2 : 0R < 1/2
  0<1/2 = halvePositive 1/2 (<WellDefined reflexive (symmetric (transitive (transitive (+WellDefined (symmetric (transitive *Commutative identIsIdent)) (symmetric (transitive *Commutative identIsIdent))) (symmetric *DistributesOver+)) 1/2is1/2)) (0<1 nontrivial))

  halfHalves : {a : A} → (1/2 * (a + a)) ∼ a
  halfHalves {a} = transitive (*WellDefined reflexive (+WellDefined (symmetric identIsIdent) (symmetric identIsIdent))) (transitive (*WellDefined reflexive (symmetric *DistributesOver+')) (transitive *Associative (transitive (*WellDefined 1/2is1/2 reflexive) identIsIdent)))

abstract
  bothNearImpliesNear : {t r s : A} (e : A) .(0<e : 0R < e) → (abs (r + inverse t) < e) → (abs (s + inverse t) < e) → abs (r + inverse s) < (e + e)
  bothNearImpliesNear {t} {r} {s} e 0<e rNearT sNearT = u
    where
      pr : ((abs (r + inverse t)) + (abs (s + inverse t))) < (e + e)
      pr = ringAddInequalities rNearT sNearT
      t' : (abs (r + inverse t) + abs (t + inverse s)) < (e + e)
      t' = <WellDefined (+WellDefined reflexive (transitive (absNegation _) (absWellDefined _ _ (transitive invContravariant (+WellDefined (invTwice _) reflexive))))) reflexive pr
      u : abs (r + inverse s) < (e + e)
      u with triangleInequality (r + inverse t) (t + inverse s)
      ... | inl t'' = <Transitive (<WellDefined (absWellDefined _ _ (transitive +Associative (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) reflexive))) reflexive t'') t'
      ... | inr eq = <WellDefined (transitive (symmetric eq) (absWellDefined _ _ (transitive +Associative (+WellDefined (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) reflexive)))) reflexive t'

private
  limitsUniqueLemma : (x : Sequence A) {r s : A} (xr : x ~> r) (xs : x ~> s) (r<s : r < s) → False
  limitsUniqueLemma x {r} {s} xr xs r<s = irreflexive (<WellDefined reflexive (symmetric prE) u')
    where
      e : A
      e = 1/2 * (s + inverse r)
      prE : (s + inverse r) ∼ (e + e)
      prE = transitive (symmetric halfHalves) *DistributesOver+
      0<e : 0R < e
      0<e = orderRespectsMultiplication 0<1/2 (moveInequality r<s)
      abstract
        N1 : ℕ
        N1 with xs e 0<e
        ... | x , _ = x
        N1prop : (n : ℕ) → (N1 <N n) → abs (index x n + inverse s) < e
        N1prop with xs e 0<e
        ... | x , pr = pr
        N2 : ℕ
        N2 with xr e 0<e
        ... | x , _ = x
        N2prop : (n : ℕ) → (N2 <N n) → abs (index x n + inverse r) < e
        N2prop with xr e 0<e
        ... | x , pr = pr
      good : ℕ
      good = succ (N1 +N N2)
      N1Good : abs (index x good + inverse s) < e
      N1Good = N1prop good (le N2 (applyEquality succ (Semiring.commutative ℕSemiring N2 N1)))
      N2Good : abs (index x good + inverse r) < e
      N2Good = N2prop good (le N1 refl)
      t : ((abs (index x good + inverse s)) + (abs (index x good + inverse r))) < (e + e)
      t = ringAddInequalities N1Good N2Good
      t' : ((abs (index x good + inverse s)) + (abs (r + inverse (index x good)))) < (e + e)
      t' = <WellDefined (+WellDefined reflexive (transitive (absNegation _) (absWellDefined _ _ (transitive invContravariant (+WellDefined (invTwice _) reflexive))))) reflexive t
      u : abs (inverse s + r) < (e + e)
      u with triangleInequality (index x good + inverse s) (r + inverse (index x good))
      ... | inl t'' = <Transitive (<WellDefined (absWellDefined _ _ (transitive groupIsAbelian (transitive +Associative (transitive (+WellDefined (symmetric +Associative) reflexive) (transitive (+WellDefined (transitive (+WellDefined reflexive invLeft) identRight) reflexive) groupIsAbelian))))) reflexive t'') t'
      ... | inr eq = <WellDefined (transitive (symmetric eq) (absWellDefined _ _ (transitive groupIsAbelian (transitive +Associative (transitive (+WellDefined (symmetric +Associative) reflexive) (transitive (+WellDefined (transitive (+WellDefined reflexive invLeft) identRight) reflexive) groupIsAbelian)))))) reflexive t'
      u' : (s + inverse r) < (e + e)
      u' = <WellDefined (transitive (absNegation _) (transitive (absWellDefined _ _ (transitive invContravariant (transitive groupIsAbelian (+WellDefined (invTwice _) reflexive)))) (symmetric (greaterZeroImpliesEqualAbs (moveInequality r<s))))) reflexive u

limitsAreUnique : (x : Sequence A) → {r s : A} → (x ~> r) → (x ~> s) → r ∼ s
limitsAreUnique x {r} {s} xr xs with totality r s
limitsAreUnique x {r} {s} xr xs | inl (inl r<s) = exFalso (limitsUniqueLemma x xr xs r<s)
limitsAreUnique x {r} {s} xr xs | inl (inr s<r) = exFalso (limitsUniqueLemma x xs xr s<r)
limitsAreUnique x {r} {s} xr xs | inr r=s = r=s

constantSequenceConverges : (a : A) → constSequence a ~> a
constantSequenceConverges a e 0<e = 0 , λ n _ → <WellDefined (symmetric (transitive (absWellDefined _ _ (transitive (+WellDefined (identityOfIndiscernablesRight _∼_ reflexive (indexAndConst a n)) reflexive) invRight)) absZeroIsZero)) reflexive 0<e
