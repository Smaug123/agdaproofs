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
open import Numbers.Primes.PrimeNumbers

module Fields.Orders.Limits.Lemmas {a b c : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {_} {c} A} {R : Ring S _+_ _*_} {pOrder : SetoidPartialOrder S _<_} {F : Field R} {pRing : PartiallyOrderedRing R pOrder} (oF : TotallyOrderedField F pRing) where

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
open import Fields.Orders.Limits.Definition oF
open import Fields.Lemmas F
open import Fields.Orders.Total.Lemmas oF
open import Rings.Characteristic R
open import Rings.InitialRing R

private
  2!=3 : 2 ≡ 3 → False
  2!=3 ()

convergentSequenceCauchy : (nontrivial : 0R ∼ 1R → False) → {a : Sequence A} → {r : A} → a ~> r → (decidedCharacteristic : ((1R + 1R) ∼ 0R) || (((1R + 1R) ∼ 0R) → False)) → cauchy a
convergentSequenceCauchy nontrivial {a} {r} a->r (inl 2=0) ε x with 1/nPositive 2 λ t → 2!=3 (characteristicWellDefined nontrivial {2} {3} twoIsPrime threeIsPrime (transitive (transitive +Associative identRight) 2=0) t)
... | 0<1/3 with allInvertible (fromN 3) λ t → 2!=3 (characteristicWellDefined nontrivial {2} {3} twoIsPrime threeIsPrime (transitive (transitive +Associative identRight) 2=0) t)
... | 1/3 , pr1/3 with a->r (1/3 * ε) (orderRespectsMultiplication 0<1/3 x)
... | N , pr = N , λ {m} {n} → ans m n
  where
    2/3 : (1/3 + 1/3) < 1R
    2/3 = <WellDefined reflexive (transitive (transitive (+WellDefined (transitive (symmetric identIsIdent) *Commutative) (transitive (+WellDefined (transitive (symmetric identIsIdent) *Commutative) (transitive (+WellDefined (symmetric (transitive *Commutative identIsIdent)) (symmetric timesZero)) (symmetric *DistributesOver+))) (symmetric *DistributesOver+))) (symmetric *DistributesOver+)) pr1/3) (<WellDefined reflexive (transitive (+WellDefined reflexive (symmetric identRight)) (symmetric +Associative)) (orderRespectsAddition (<WellDefined identLeft reflexive (orderRespectsAddition 0<1/3 1/3)) 1/3))
    ans : (m n : ℕ) → N <N m → N <N n → abs (index a m + inverse (index a n)) < ε
    ans m n N<m N<n = <Transitive (bothNearImpliesNear {r} (1/3 * ε) (orderRespectsMultiplication 0<1/3 x) (pr m N<m) (pr n N<n)) (<WellDefined *DistributesOver+' identIsIdent (ringCanMultiplyByPositive x 2/3))
convergentSequenceCauchy _ {a} {r} a->r (inr 2!=0) e 0<e with halve 2!=0 e
... | e/2 , prE/2 with a->r e/2 (halvePositive' prE/2 0<e)
... | N , pr = N , λ {m} {n} → ans m n
  where
    ans : (m n : ℕ) → N <N m → N <N n → abs (index a m + inverse (index a n)) < e
    ans m n N<m N<n = <WellDefined reflexive prE/2 (bothNearImpliesNear {r} e/2 (halvePositive' prE/2 0<e) (pr m N<m) (pr n N<n))
