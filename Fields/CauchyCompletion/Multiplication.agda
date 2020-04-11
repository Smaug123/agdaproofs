{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Setoids.Setoids
open import Rings.Definition
open import Rings.Lemmas
open import Rings.Orders.Partial.Definition
open import Rings.Orders.Total.Definition
open import Groups.Definition
open import Groups.Lemmas
open import Fields.Fields
open import Sets.EquivalenceRelations
open import Sequences
open import Setoids.Orders
open import Functions
open import LogicalFormulae
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Naturals.Order.Lemmas

module Fields.CauchyCompletion.Multiplication {m n o : _} {A : Set m} {S : Setoid {m} {n} A} {_+_ : A → A → A} {_*_ : A → A → A} {_<_ : Rel {m} {o} A} {pOrder : SetoidPartialOrder S _<_} {R : Ring S _+_ _*_} {pRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pRing) (F : Field R) (charNot2 : Setoid._∼_ S ((Ring.1R R) + (Ring.1R R)) (Ring.0R R) → False) where

open Setoid S
open SetoidTotalOrder (TotallyOrderedRing.total order)
open SetoidPartialOrder pOrder
open Equivalence eq
open PartiallyOrderedRing pRing
open Ring R
open Group additiveGroup
open Field F
open import Fields.Orders.Lemmas {F = F} record { oRing = order }

open import Fields.Lemmas F
open import Rings.Orders.Partial.Lemmas pRing
open import Rings.Orders.Total.Lemmas order
open import Fields.CauchyCompletion.Definition order F
open import Fields.CauchyCompletion.Setoid order F charNot2
open import Fields.CauchyCompletion.Approximation order F charNot2

0!=1 : {e : A} → (0G < e) → 0R ∼ 1R → False
0!=1 {e} 0<e 0=1 = irreflexive (<WellDefined (Equivalence.reflexive eq) (oneZeroImpliesAllZero R 0=1) 0<e)

private
  littleLemma : {a b c d : A} → ((a * b) + inverse (c * d)) ∼ ((a * (b + inverse d)) + (d * (a + inverse c)))
  littleLemma {a} {b} {c} {d} = Equivalence.transitive eq (Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq identLeft) (+WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (+WellDefined (Equivalence.transitive eq (ringMinusExtracts R) (inverseWellDefined additiveGroup *Commutative)) (Equivalence.reflexive eq)) (invLeft {d * a}))) (Equivalence.transitive eq (Equivalence.symmetric eq (ringMinusExtracts' R)) *Commutative))) (Equivalence.symmetric eq +Associative))) (+Associative)) (Equivalence.symmetric eq (+WellDefined (*DistributesOver+) (*DistributesOver+)))

_*C_ : CauchyCompletion → CauchyCompletion → CauchyCompletion
CauchyCompletion.elts (record { elts = a ; converges = aConv } *C record { elts = b ; converges = bConv }) = apply _*_ a b
CauchyCompletion.converges (record { elts = a ; converges = aConv } *C record { elts = b ; converges = bConv }) e 0<e with boundModulus record { elts = a ; converges = aConv }
... | aBound , (Na , prABound) with boundModulus record { elts = b ; converges = bConv }
... | bBound , (Nb , prBBound) = N , ans
  where
    boundBoth : A
    boundBoth = aBound + bBound
    abstract
      ab<bb : aBound < boundBoth
      ab<bb = <WellDefined identLeft groupIsAbelian (orderRespectsAddition {0R} {bBound} (greaterThanAbsImpliesGreaterThan0 (prBBound (succ Nb) (le 0 refl))) aBound)
      bb<bb : bBound < boundBoth
      bb<bb = <WellDefined identLeft (Equivalence.reflexive eq) (orderRespectsAddition {0R} {aBound} (greaterThanAbsImpliesGreaterThan0 (prABound (succ Na) (le 0 refl))) bBound)
      0<boundBoth : 0R < boundBoth
      0<boundBoth = <WellDefined identLeft (Equivalence.reflexive eq) (ringAddInequalities (greaterThanAbsImpliesGreaterThan0 (prABound (succ Na) (le 0 refl))) (greaterThanAbsImpliesGreaterThan0 (prBBound (succ Nb) (le 0 refl))))
    abstract
      1/boundBoothAndPr : Sg A λ i → i * (aBound + bBound) ∼ 1R
      1/boundBoothAndPr = allInvertible boundBoth λ pr → irreflexive (<WellDefined (Equivalence.reflexive eq) pr 0<boundBoth)
      1/boundBooth : A
      1/boundBooth with 1/boundBoothAndPr
      ... | a , _ = a
      1/boundBoothPr : 1/boundBooth * (aBound + bBound) ∼ 1R
      1/boundBoothPr with 1/boundBoothAndPr
      ... | _ , pr = pr
      0<1/boundBooth : 0G < 1/boundBooth
      0<1/boundBooth = inversePositiveIsPositive 1/boundBoothPr 0<boundBoth
    abstract
      miniEAndPr : Sg A (λ i → (i + i) ∼ (e * 1/boundBooth))
      miniEAndPr = halve charNot2 (e * 1/boundBooth)
      miniE : A
      miniE with miniEAndPr
      ... | a , _ = a
      miniEPr : (miniE + miniE) ∼ (e * 1/boundBooth)
      miniEPr with miniEAndPr
      ... | _ , pr = pr
      0<miniE : 0R < miniE
      0<miniE = halvePositive miniE (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq miniEPr) (orderRespectsMultiplication 0<e 0<1/boundBooth))
    abstract
      reallyNAAndPr : Sg ℕ (λ N → {m n : ℕ} → N <N m → N <N n → abs (index a m + inverse (index a n)) < miniE)
      reallyNAAndPr = aConv miniE 0<miniE
      reallyNa : ℕ
      reallyNa with reallyNAAndPr
      ... | a , _ = a
      reallyNaPr : {m n : ℕ} → reallyNa <N m → reallyNa <N n → abs (index a m + inverse (index a n)) < miniE
      reallyNaPr with reallyNAAndPr
      ... | _ , pr = pr
      reallyNBAndPr : Sg ℕ (λ N → {m n : ℕ} → N <N m → N <N n → abs (index b m + inverse (index b n)) < miniE)
      reallyNBAndPr = bConv miniE 0<miniE
      reallyNb : ℕ
      reallyNb with reallyNBAndPr
      ... | a , _ = a
      reallyNbPr : {m n : ℕ} → reallyNb <N m → reallyNb <N n → abs (index b m + inverse (index b n)) < miniE
      reallyNbPr with reallyNBAndPr
      ... | _ , pr = pr
    N : ℕ
    N = (Na +N (Nb +N (reallyNa +N reallyNb)))
    ans : {m : ℕ} {n : ℕ} → N <N m → N <N n → abs (index (apply _*_ a b) m + inverse (index (apply _*_ a b) n)) < e
    ans {m} {n} N<m N<n rewrite indexAndApply a b _*_ {m} | indexAndApply a b _*_ {n} = ans'''
      where
        Na<m : Na <N m
        Na<m = inequalityShrinkLeft N<m
        Nb<n : Nb <N n
        Nb<n = inequalityShrinkLeft (inequalityShrinkRight {Na} N<n)
        abstract
          sum : {m n : ℕ} → (reallyNa +N reallyNb) <N m → (reallyNa +N reallyNb) <N n → (boundBoth * ((abs (index b m + inverse (index b n))) + (abs (index a m + inverse (index a n))))) < e
          sum {m} {n} <m <n = <WellDefined *Commutative (Equivalence.transitive eq (*WellDefined miniEPr (Equivalence.reflexive eq)) (Equivalence.transitive eq (Equivalence.symmetric eq *Associative) (Equivalence.transitive eq (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) 1/boundBoothPr) *Commutative) (identIsIdent)))) (ringCanMultiplyByPositive {c = boundBoth} 0<boundBoth (ringAddInequalities (reallyNbPr {m} {n} (inequalityShrinkRight <m) (inequalityShrinkRight <n)) (reallyNaPr {m} {n} (inequalityShrinkLeft <m) (inequalityShrinkLeft <n))))
        q : ((boundBoth * (abs (index b m + inverse (index b n)))) + (boundBoth * (abs (index a m + inverse (index a n))))) < e
        q = <WellDefined *DistributesOver+ (Equivalence.reflexive eq) (sum {m} {n} (inequalityShrinkRight {Nb} (inequalityShrinkRight {Na} N<m)) (inequalityShrinkRight {Nb} (inequalityShrinkRight {Na} N<n)))
        p : ((abs (index a m) * abs (index b m + inverse (index b n))) + (abs (index b n) * abs (index a m + inverse (index a n)))) < e
        p with totality 0R (index b m + inverse (index b n))
        p | inl (inl 0<bm-bn) with totality 0R (index a m + inverse (index a n))
        p | inl (inl 0<bm-bn) | inl (inl 0<am-an) = SetoidPartialOrder.<Transitive pOrder (ringAddInequalities (<WellDefined (Equivalence.reflexive eq) (*WellDefined (Equivalence.reflexive eq) (greaterZeroImpliesEqualAbs 0<bm-bn)) (ringCanMultiplyByPositive 0<bm-bn (SetoidPartialOrder.<Transitive pOrder (prABound m Na<m) ab<bb))) (<WellDefined (Equivalence.reflexive eq) (*WellDefined (Equivalence.reflexive eq) (greaterZeroImpliesEqualAbs 0<am-an)) (ringCanMultiplyByPositive 0<am-an (SetoidPartialOrder.<Transitive pOrder (prBBound n Nb<n) bb<bb)))) q
        p | inl (inl 0<bm-bn) | inl (inr am-an<0) = SetoidPartialOrder.<Transitive pOrder (ringAddInequalities (<WellDefined (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (greaterZeroImpliesEqualAbs 0<bm-bn))) (Equivalence.reflexive eq) (ringCanMultiplyByPositive (<WellDefined (Equivalence.reflexive eq) (greaterZeroImpliesEqualAbs 0<bm-bn) 0<bm-bn) (SetoidPartialOrder.<Transitive pOrder (prABound m Na<m) ab<bb))) (<WellDefined (*WellDefined (Equivalence.reflexive eq) (lessZeroImpliesEqualNegAbs am-an<0)) (Equivalence.reflexive eq) (ringCanMultiplyByPositive (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (lessZeroImpliesEqualNegAbs am-an<0)) (lemm2 _ am-an<0)) (SetoidPartialOrder.<Transitive pOrder (prBBound n Nb<n) bb<bb)))) q
        p | inl (inl 0<bm-bn) | inr 0=am-an = <WellDefined (+WellDefined (Equivalence.reflexive eq) (*WellDefined (Equivalence.reflexive eq) 0=am-an)) (Equivalence.reflexive eq) (<WellDefined (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq timesZero)) (Equivalence.reflexive eq) (<WellDefined (Equivalence.symmetric eq identRight) (Equivalence.reflexive eq) (SetoidPartialOrder.<Transitive pOrder (<WellDefined (Equivalence.reflexive eq) (+WellDefined (Equivalence.reflexive eq) (*WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (Equivalence.symmetric eq absZeroIsZero) (absWellDefined _ _ 0=am-an)))) (<WellDefined (Equivalence.reflexive eq) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq timesZero)) (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq identRight) (<WellDefined (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (greaterZeroImpliesEqualAbs 0<bm-bn))) (Equivalence.reflexive eq) (ringCanMultiplyByPositive (<WellDefined (Equivalence.reflexive eq) (greaterZeroImpliesEqualAbs 0<bm-bn) 0<bm-bn) (SetoidPartialOrder.<Transitive pOrder (prABound m Na<m) ab<bb)))))) q)))
        p | inl (inr bm-bn<0) = SetoidPartialOrder.<Transitive pOrder ans'' q
          where
            bar : ((abs (index a m)) * (inverse (index b m + inverse (index b n)))) < (boundBoth * abs (index b m + inverse (index b n)))
            bar = <WellDefined (*WellDefined (Equivalence.reflexive eq) (lessZeroImpliesEqualNegAbs bm-bn<0)) (Equivalence.reflexive eq) (ringCanMultiplyByPositive (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq (lessZeroImpliesEqualNegAbs bm-bn<0)) (lemm2 _ bm-bn<0)) (SetoidPartialOrder.<Transitive pOrder (prABound m Na<m) (ab<bb)))
            foo : (((abs (index b n)) * (abs (index a m + inverse (index a n)))) < (boundBoth * abs (index a m + inverse (index a n)))) || (((abs (index b n)) * (abs (index a m + inverse (index a n)))) ∼ (boundBoth * abs (index a m + inverse (index a n))))
            foo with totality 0R (index a m + inverse (index a n))
            foo | inl (inl 0<am-an) = inl (ringCanMultiplyByPositive 0<am-an (SetoidPartialOrder.<Transitive pOrder (prBBound n Nb<n) bb<bb))
            foo | inl (inr am-an<0) = inl (ringCanMultiplyByPositive (lemm2 _ am-an<0) (SetoidPartialOrder.<Transitive pOrder (prBBound n Nb<n) bb<bb))
            foo | inr 0=am-an = inr (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=am-an)) (Equivalence.transitive eq (Equivalence.transitive eq timesZero (Equivalence.symmetric eq timesZero)) (*WellDefined (Equivalence.reflexive eq) 0=am-an)))
            ans'' : _
            ans'' with foo
            ... | inl pr = ringAddInequalities bar pr
            ... | inr pr = <WellDefined (Equivalence.reflexive eq) (+WellDefined (Equivalence.reflexive eq) pr) (orderRespectsAddition bar ((abs (index b n)) * (abs (index a m + inverse (index a n)))))
        p | inr 0=bm-bn = ans''
          where
            bar : (boundBoth * abs (index b m + inverse (index b n))) ∼ 0R
            bar = Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.symmetric eq 0=bm-bn)) (absZeroIsZero))) timesZero
            bar' : (abs (index a m) * (index b m + inverse (index b n))) ∼ 0R
            bar' = Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=bm-bn)) timesZero
            foo : (((abs (index b n)) * (abs (index a m + inverse (index a n)))) < (boundBoth * abs (index a m + inverse (index a n)))) || (0R ∼ (index a m + inverse (index a n)))
            foo with totality 0R (index a m + inverse (index a n))
            foo | inl (inl 0<am-an) = inl (SetoidPartialOrder.<Transitive pOrder (ringCanMultiplyByPositive 0<am-an (prBBound n Nb<n)) (ringCanMultiplyByPositive 0<am-an bb<bb))
            foo | inl (inr am-an<0) = inl (SetoidPartialOrder.<Transitive pOrder (ringCanMultiplyByPositive (lemm2 _ am-an<0) (prBBound n Nb<n)) (ringCanMultiplyByPositive (lemm2 _ am-an<0) bb<bb))
            foo | inr 0=am-an = inr 0=am-an
            ans'' : _
            ans'' with foo
            ... | inl pr = SetoidPartialOrder.<Transitive pOrder (<WellDefined groupIsAbelian groupIsAbelian (<WellDefined (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq bar')) (+WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq bar)) (orderRespectsAddition pr 0R))) q
            ... | inr pr = <WellDefined (Equivalence.transitive eq (Equivalence.symmetric eq identRight) (+WellDefined (Equivalence.symmetric eq bar') (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.transitive eq (absWellDefined _ _ (Equivalence.symmetric eq pr)) absZeroIsZero)) timesZero)))) (Equivalence.reflexive eq) 0<e
        ans''' : abs ((index a m * index b m) + inverse (index a n * index b n)) < e
        ans''' with triangleInequality (index a m * (index b m + inverse (index b n))) (index b n * (index a m + inverse (index a n)))
        ... | inl less = <WellDefined (Equivalence.symmetric eq (absWellDefined ((index a m * index b m) + (inverse (index a n * index b n))) (((index a m) * (index b m + (inverse (index b n)))) + ((index b n) * (index a m + inverse (index a n)))) littleLemma)) (Equivalence.reflexive eq) (SetoidPartialOrder.<Transitive pOrder less (<WellDefined (+WellDefined (Equivalence.symmetric eq (absRespectsTimes (index a m) _)) (Equivalence.symmetric eq (absRespectsTimes (index b n) _))) (Equivalence.reflexive eq) p))
        ... | inr equal = <WellDefined {_ + _} {abs _} {e} {e} (symmetric (transitive (transitive (absWellDefined ((index a m * index b m) + (inverse (index a n * index b n))) (((index a m) * (index b m + (inverse (index b n)))) + ((index b n) * (index a m + inverse (index a n)))) littleLemma) equal) (+WellDefined (absRespectsTimes (index a m) _) (absRespectsTimes (index b n) _)))) reflexive p

*CCommutative : {a b : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid (a *C b) (b *C a)
*CCommutative {a} {b} ε 0<e = 0 , ans
  where
    foo : {x y : A} → (x * y) + inverse (y * x) ∼ 0G
    foo = Equivalence.transitive eq (+WellDefined (Equivalence.reflexive eq) (inverseWellDefined additiveGroup *Commutative)) invRight
    ans : {m : ℕ} → 0 <N m → abs (index (apply _+_ (CauchyCompletion.elts (a *C b)) (map inverse (CauchyCompletion.elts (b *C a)))) m) < ε
    ans {m} 0<m rewrite indexAndApply (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts b)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts a))) _+_ {m} | indexAndApply (CauchyCompletion.elts a) (CauchyCompletion.elts b) _*_ {m} | equalityCommutative (mapAndIndex (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts a)) inverse m) | indexAndApply (CauchyCompletion.elts b) (CauchyCompletion.elts a) _*_ {m} = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (absWellDefined _ _ foo) (identityOfIndiscernablesRight _∼_ (Equivalence.reflexive eq) absZero))) (Equivalence.reflexive eq) 0<e

abstract

  multiplicationWellDefinedLeft' : (0!=1 : 0R ∼ 1R → False) (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C c)
  multiplicationWellDefinedLeft' 0!=1 a b c a=b ε 0<e = N , ans
    where
      abstract
        cBoundAndPr : Sg A (λ b → Sg ℕ (λ N → (m : ℕ) → (N <N m) → (abs (index (CauchyCompletion.elts c) m)) < b))
        cBoundAndPr = boundModulus c
        cBound : A
        cBound with cBoundAndPr
        ... | a , _ = a
        cBoundN : ℕ
        cBoundN with cBoundAndPr
        ... | _ , (N , _) = N
        cBoundPr : (m : ℕ) → (cBoundN <N m) → (abs (index (CauchyCompletion.elts c) m)) < cBound
        cBoundPr with cBoundAndPr
        ... | _ , (_ , pr) = pr
      0<cBound : 0G < cBound
      0<cBound with totality 0G cBound
      0<cBound | inl (inl 0<cBound) = 0<cBound
      0<cBound | inl (inr cBound<0) = exFalso (absNonnegative (SetoidPartialOrder.<Transitive pOrder (cBoundPr (succ cBoundN) (le 0 refl)) cBound<0))
      0<cBound | inr 0=cBound = exFalso (absNonnegative (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=cBound) (cBoundPr (succ cBoundN) (le 0 refl))))
      e/c : A
      e/c with allInvertible cBound (λ pr → irreflexive (<WellDefined (Equivalence.reflexive eq) pr 0<cBound))
      ... | (1/c , _) = ε * 1/c
      e/cPr : e/c * cBound ∼ ε
      e/cPr with allInvertible cBound (λ pr → irreflexive (<WellDefined (Equivalence.reflexive eq) pr 0<cBound))
      ... | (1/c , pr) = Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.transitive eq (Equivalence.symmetric eq *Associative) (*WellDefined (Equivalence.reflexive eq) pr)) *Commutative) (identIsIdent)
      0<e/c : 0G < e/c
      0<e/c = ringCanCancelPositive {0G} {e/c} 0<cBound (<WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq *Commutative timesZero)) (Equivalence.symmetric eq e/cPr) 0<e)
      abBound : ℕ
      abBound with a=b e/c 0<e/c
      ... | Na=b , _ = Na=b
      abPr : {m : ℕ} → (abBound <N m) → abs (index (apply _+_ (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b))) m) < e/c
      abPr with a=b e/c 0<e/c
      ... | Na=b , pr = pr
      N : ℕ
      N = abBound +N cBoundN
      cBounded : (m : ℕ) → (N <N m) → abs (index (CauchyCompletion.elts c) m) < cBound
      cBounded m N<m = cBoundPr m (inequalityShrinkRight N<m)
      a-bSmall : (m : ℕ) → N <N m → abs ((index (CauchyCompletion.elts a) m) + inverse (index (CauchyCompletion.elts b) m)) < e/c
      a-bSmall m N<m = <WellDefined (absWellDefined _ _ (transitive (identityOfIndiscernablesLeft _∼_ reflexive (equalityCommutative (indexAndApply (CauchyCompletion.elts a) (map inverse (CauchyCompletion.elts b)) _+_ {m}))) (+WellDefined reflexive (identityOfIndiscernablesLeft _∼_ reflexive (mapAndIndex (CauchyCompletion.elts b) inverse m))))) reflexive (abPr {m} (inequalityShrinkLeft N<m))
      ans : {m : ℕ} → N <N m → abs (index (apply _+_ (apply _*_ (CauchyCompletion.elts a) (CauchyCompletion.elts c)) (map inverse (apply _*_ (CauchyCompletion.elts b) (CauchyCompletion.elts c)))) m) < ε
      ans {m} N<m = <WellDefined (absWellDefined _ _ (transitive (+WellDefined (identityOfIndiscernablesLeft _∼_ reflexive (indexAndApply _ _ _*_ {m})) (transitive (transitive (ringMinusExtracts' R) (inverseWellDefined additiveGroup (identityOfIndiscernablesRight _∼_ reflexive (equalityCommutative (indexAndApply _ _ _*_ {m}))))) (identityOfIndiscernablesLeft _∼_ reflexive (equalityCommutative (mapAndIndex _ inverse m))))) (identityOfIndiscernablesLeft _∼_ reflexive (indexAndApply _ _ _+_ {m})))) reflexive (<WellDefined (absWellDefined ((index (CauchyCompletion.elts a) m + inverse (index (CauchyCompletion.elts b) m)) * index (CauchyCompletion.elts c) m) _ (Equivalence.transitive eq (Equivalence.transitive eq *Commutative *DistributesOver+) (+WellDefined *Commutative *Commutative))) (Equivalence.reflexive eq) (<WellDefined (Equivalence.symmetric eq (absRespectsTimes _ _)) (Equivalence.reflexive eq) (<WellDefined (Equivalence.reflexive eq) e/cPr (ans' (index (CauchyCompletion.elts a) m) (index (CauchyCompletion.elts b) m) (index (CauchyCompletion.elts c) m) (a-bSmall m N<m) (cBounded m N<m)))))
        where
          ans' : (a b c : A) → abs (a + inverse b) < e/c → abs c < cBound → (abs (a + inverse b) * abs c) < (e/c * cBound)
          ans' a b c a-b<e/c c<bound with totality 0R c
          ans' a b c a-b<e/c c<bound | inl (inl 0<c) with totality 0G (a + inverse b)
          ans' a b c a-b<e/c c<bound | inl (inl 0<c) | inl (inl 0<a-b) = ringMultiplyPositives 0<a-b 0<c a-b<e/c c<bound
          ans' a b c a-b<e/c c<bound | inl (inl 0<c) | inl (inr a-b<0) = ringMultiplyPositives (lemm2 (a + inverse b) a-b<0) 0<c a-b<e/c c<bound
          ans' a b c a-b<e/c c<bound | inl (inl 0<c) | inr 0=a-b = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a-b) (Equivalence.reflexive eq)) (Equivalence.transitive eq *Commutative timesZero))) (Equivalence.reflexive eq) (orderRespectsMultiplication 0<e/c 0<cBound)
          ans' a b c a-b<e/c c<bound | inl (inr c<0) with totality 0G (a + inverse b)
          ans' a b c a-b<e/c c<bound | inl (inr c<0) | inl (inl 0<a-b) = ringMultiplyPositives 0<a-b (lemm2 c c<0) a-b<e/c c<bound
          ans' a b c a-b<e/c c<bound | inl (inr c<0) | inl (inr a-b<0) = ringMultiplyPositives (lemm2 (a + inverse b) a-b<0) (lemm2 c c<0) a-b<e/c c<bound
          ans' a b c a-b<e/c c<bound | inl (inr c<0) | inr 0=a-b = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.symmetric eq 0=a-b) (Equivalence.reflexive eq)) (Equivalence.transitive eq *Commutative timesZero))) (Equivalence.reflexive eq) (orderRespectsMultiplication 0<e/c 0<cBound)
          ans' a b c a-b<e/c c<bound | inr 0=c = <WellDefined (Equivalence.symmetric eq (Equivalence.transitive eq (*WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq 0=c)) timesZero)) (Equivalence.reflexive eq) (orderRespectsMultiplication 0<e/c 0<cBound)


  multiplicationWellDefinedLeft : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C c)
  multiplicationWellDefinedLeft with totality 0R 1R
  ... | inl (inl 0<1') = multiplicationWellDefinedLeft' (λ pr → irreflexive {0G} (<WellDefined (Equivalence.reflexive eq) (Equivalence.symmetric eq pr) 0<1'))
  ... | inl (inr 1<0) = multiplicationWellDefinedLeft' (λ pr → irreflexive {0G} (<WellDefined (Equivalence.symmetric eq pr) (Equivalence.reflexive eq) 1<0))
  ... | inr (0=1) = λ a b c a=b → Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C c} {injection 0G} {b *C c} (Equivalence.symmetric (Setoid.eq cauchyCompletionSetoid) {injection 0G} {a *C c} (trivialIfInputTrivial 0=1 (a *C c))) (trivialIfInputTrivial 0=1 (b *C c))

  multiplicationPreservedLeft : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (injection a *C c) (injection b *C c)
  multiplicationPreservedLeft {a} {b} {c} a=b = multiplicationWellDefinedLeft (injection a) (injection b) c (injectionPreservesSetoid a b a=b)

  multiplicationPreservedRight : {a b : A} {c : CauchyCompletion} → (a ∼ b) → Setoid._∼_ cauchyCompletionSetoid (c *C injection a) (c *C injection b)
  multiplicationPreservedRight {a} {b} {c} a=b = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {c *C injection a} {injection a *C c} {c *C injection b} (*CCommutative {c} {injection a}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a *C c} {injection b *C c} {c *C injection b} (multiplicationPreservedLeft {a} {b} {c} a=b) (*CCommutative {injection b} {c}))

  multiplicationPreserved : {a b c d : A} → (a ∼ b) → (c ∼ d) → Setoid._∼_ cauchyCompletionSetoid (injection a *C injection c) (injection b *C injection d)
  multiplicationPreserved {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {injection a *C injection c} {injection a *C injection d} {injection b *C injection d} (multiplicationPreservedRight {c} {d} {injection a} c=d) (multiplicationPreservedLeft {a} {b} {injection d} a=b)

  multiplicationWellDefinedRight : (a b c : CauchyCompletion) → Setoid._∼_ cauchyCompletionSetoid b c → Setoid._∼_ cauchyCompletionSetoid (a *C b) (a *C c)
  multiplicationWellDefinedRight a b c b=c = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C b} {b *C a} {a *C c} (*CCommutative {a} {b}) (Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {b *C a} {c *C a} {a *C c} (multiplicationWellDefinedLeft b c a b=c) (*CCommutative {c} {a}))

  multiplicationWellDefined : {a b c d : CauchyCompletion} → Setoid._∼_ cauchyCompletionSetoid a b → Setoid._∼_ cauchyCompletionSetoid c d → Setoid._∼_ cauchyCompletionSetoid (a *C c) (b *C d)
  multiplicationWellDefined {a} {b} {c} {d} a=b c=d = Equivalence.transitive (Setoid.eq cauchyCompletionSetoid) {a *C c} {a *C d} {b *C d} (multiplicationWellDefinedRight a c d c=d) (multiplicationWellDefinedLeft a b d a=b)
