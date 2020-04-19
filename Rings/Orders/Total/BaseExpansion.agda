{-# OPTIONS --safe --warning=error --without-K --guardedness #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import LogicalFormulae
open import Groups.Lemmas
open import Groups.Definition
open import Setoids.Orders.Partial.Definition
open import Setoids.Orders.Total.Definition
open import Setoids.Setoids
open import Functions.Definition
open import Sets.EquivalenceRelations
open import Rings.Definition
open import Rings.Orders.Total.Definition
open import Rings.Orders.Partial.Definition
open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Numbers.Modulo.Definition
open import Semirings.Definition
open import Orders.Total.Definition
open import Sequences

-- Note: totality is necessary here. The construction of a base-n expansion fundamentally relies on being able to take floors.

module Rings.Orders.Total.BaseExpansion {a m p : _} {A : Set a} {S : Setoid {a} {m} A} {_+_ : A → A → A} {_*_ : A → A → A} {R : Ring S _+_ _*_} {_<_ : Rel {_} {p} A} {pOrder : SetoidPartialOrder S _<_} {pOrderRing : PartiallyOrderedRing R pOrder} (order : TotallyOrderedRing pOrderRing) {n : ℕ} (1<n : 1 <N n) where

open Ring R
open Group additiveGroup
open Setoid S
open Equivalence eq
open SetoidPartialOrder pOrder
open TotallyOrderedRing order
open SetoidTotalOrder total
open PartiallyOrderedRing pOrderRing
open import Rings.Lemmas R
open import Rings.Orders.Partial.Lemmas pOrderRing
open import Rings.Orders.Total.Lemmas order
open import Rings.InitialRing R
open import Rings.IntegralDomains.Lemmas

record FloorIs (a : A) (n : ℕ) : Set (m ⊔ p) where
  field
    prBelow : fromN n <= a
    prAbove : a < fromN (succ n)

addOneToFloor : {a : A} {n : ℕ} → FloorIs a n → FloorIs (a + 1R) (succ n)
FloorIs.prBelow (addOneToFloor record { prBelow = (inl x) ; prAbove = prAbove }) = inl (<WellDefined groupIsAbelian reflexive (orderRespectsAddition x 1R))
FloorIs.prBelow (addOneToFloor record { prBelow = (inr x) ; prAbove = prAbove }) = inr (transitive groupIsAbelian (+WellDefined x reflexive))
FloorIs.prAbove (addOneToFloor record { prBelow = x ; prAbove = prAbove }) = <WellDefined reflexive groupIsAbelian (orderRespectsAddition prAbove 1R)

private
  0<n : {x y : A} → (x < y) → 0R < fromN n
  0<n x<y = fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial x<y)) (lessTransitive (succIsPositive 0) 1<n)

  0<aFromN : {a : A} → (0<a : 0R < a) → 0R < (a * fromN n)
  0<aFromN 0<a = orderRespectsMultiplication 0<a (0<n 0<a)

  floorWellDefinedLemma : {a : A} {n1 n2 : ℕ} → FloorIs a n1 → FloorIs a n2 → n1 <N n2 → False
  floorWellDefinedLemma {a} {n1} {n2} record { prAbove = prAbove1 } record { prBelow = inl prBelow } n1<n2 with TotalOrder.totality ℕTotalOrder (succ n1) n2
  ... | inl (inl n1+1<n2) = irreflexive (<Transitive prAbove1 (<Transitive (fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial prBelow)) n1+1<n2) prBelow))
  ... | inl (inr n2<n1+1) = noIntegersBetweenXAndSuccX n1 n1<n2 n2<n1+1
  ... | inr refl = irreflexive (<Transitive prAbove1 prBelow)
  floorWellDefinedLemma {a} {n1} {n2} record { prBelow = (inl x) ; prAbove = prAbove1 } record { prBelow = (inr eq) ; prAbove = _ } n1<n2 with TotalOrder.totality ℕTotalOrder (succ n1) n2
  ... | inl (inl n1+1<n2) = irreflexive (<Transitive prAbove1 (<WellDefined reflexive eq (fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial prAbove1)) n1+1<n2)))
  ... | inl (inr n2<n1+1) = noIntegersBetweenXAndSuccX n1 n1<n2 n2<n1+1
  ... | inr refl = irreflexive (<WellDefined reflexive eq prAbove1)
  floorWellDefinedLemma {a} {n1} {n2} record { prBelow = (inr x) ; prAbove = prAbove1 } record { prBelow = (inr eq) ; prAbove = _ } n1<n2 = lessIrreflexive {n1} (fromNPreservesOrder' (anyComparisonImpliesNontrivial prAbove1) (<WellDefined reflexive (transitive eq (symmetric x)) (fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial prAbove1)) n1<n2)))

  floorWellDefined : {a : A} {n1 n2 : ℕ} → FloorIs a n1 → FloorIs a n2 → n1 ≡ n2
  floorWellDefined {a} {n1} {n2} record { prBelow = prBelow1 ; prAbove = prAbove1 } record { prBelow = prBelow ; prAbove = prAbove } with TotalOrder.totality ℕTotalOrder n1 n2
  ... | inr x = x
  floorWellDefined {a} {n1} {n2} f1 f2 | inl (inl x) = exFalso (floorWellDefinedLemma f1 f2 x)
  floorWellDefined {a} {n1} {n2} f1 f2 | inl (inr x) = exFalso (floorWellDefinedLemma f2 f1 x)

  floorWellDefined' : {a b : A} {n : ℕ} → (a ∼ b) → FloorIs a n → FloorIs b n
  FloorIs.prBelow (floorWellDefined' {a} {b} {n} a=b record { prBelow = (inl x) ; prAbove = s }) = inl (<WellDefined reflexive a=b x)
  FloorIs.prBelow (floorWellDefined' {a} {b} {n} a=b record { prBelow = (inr x) ; prAbove = s }) = inr (transitive x a=b)
  FloorIs.prAbove (floorWellDefined' {a} {b} {n} a=b record { prBelow = t ; prAbove = s }) = <WellDefined a=b reflexive s

  computeFloor' : {k : ℕ} → (fuel : ℕ) → .(k +N fuel ≡ n) → (a : A) → (0R < a) → .(a < fromN k) → Sg ℕ (FloorIs a)
  computeFloor' {zero} zero pr a 0<a a<f = exFalso (lessIrreflexive (lessTransitive 1<n (le 0 (applyEquality succ (equalityCommutative pr)))))
  computeFloor' {zero} (succ k) pr a 0<a a<f = exFalso (irreflexive (<Transitive 0<a a<f))
  computeFloor' {succ k} n pr a 0<a a<f with totality 1R a
  ... | inl (inr a<1) = 0 , (record { prAbove = <WellDefined reflexive (symmetric identRight) a<1 ; prBelow = inl 0<a })
  ... | inr 1=a = 1 , (record { prAbove = <WellDefined (transitive identRight 1=a) reflexive (fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial 0<a)) {1} (le 0 refl)) ; prBelow = inr (transitive identRight 1=a) })
  ... | inl (inl 1<a) with computeFloor' {k} (succ n) (transitivity (transitivity (Semiring.commutative ℕSemiring k (succ n)) (applyEquality succ (Semiring.commutative ℕSemiring n k))) pr) (a + inverse 1R) (moveInequality 1<a) (<WellDefined reflexive (transitive groupIsAbelian (transitive +Associative (transitive (+WellDefined invLeft reflexive) identLeft))) (orderRespectsAddition a<f (inverse 1R)))
  ... | N , snd = succ N , floorWellDefined' (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) (addOneToFloor snd)

computeFloor : (a : A) → (0R < a) → .(a < fromN n) → Sg (ℤn n (lessTransitive (succIsPositive 0) 1<n)) (λ z → FloorIs a (ℤn.x z))
computeFloor a 0<a a<n with computeFloor' {n} 0 (Semiring.sumZeroRight ℕSemiring n) a 0<a a<n
... | floor , record { prBelow = inl p ; prAbove = prAbove } = record { x = floor ; xLess = fromNPreservesOrder' (anyComparisonImpliesNontrivial 0<a) (<Transitive p a<n) } , record { prBelow = inl p ; prAbove = prAbove }
... | floor , record { prBelow = inr p ; prAbove = prAbove } = record { x = floor ; xLess = fromNPreservesOrder' (anyComparisonImpliesNontrivial 0<a) (<WellDefined (symmetric p) reflexive a<n) } , record { prBelow = inr p ; prAbove = prAbove }

firstDigit : (a : A) → 0R < a → .(a < 1R) → ℤn n (lessTransitive (succIsPositive 0) 1<n)
firstDigit a 0<a a<1 = underlying (computeFloor (a * fromN n) (orderRespectsMultiplication 0<a (0<n 0<a)) (<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1)))

baseNExpansion : (a : A) → 0R < a → .(a < 1R) → Sequence (ℤn n (lessTransitive (succIsPositive 0) 1<n))
Sequence.head (baseNExpansion a 0<a a<1) = firstDigit a 0<a a<1
Sequence.tail (baseNExpansion a 0<a a<1) with computeFloor (a * fromN n) (0<aFromN 0<a) (<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1))
... | record { x = x ; xLess = xLess } , record { prBelow = inl prB ; prAbove = prA } = baseNExpansion ((a * fromN n) + inverse (fromN x)) (moveInequality prB) (<WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) (orderRespectsAddition prA (inverse (fromN x))))
... | record { x = x ; xLess = xLess } , record { prBelow = inr prB ; prAbove = prA } = constSequence (record { x = 0 ; xLess = lessTransitive (succIsPositive 0) 1<n })

private
  powerSeq : (i : A) → (start : A) → Sequence A
  Sequence.head (powerSeq i start) = start
  Sequence.tail (powerSeq i start) = powerSeq i (start * i)

  powerSeqInduction : (i : A) (start : A) → (m : ℕ) → (index (powerSeq i start) (succ m)) ∼ i * (index (powerSeq i start) m)
  powerSeqInduction i start zero = *Commutative
  powerSeqInduction i start (succ m) = powerSeqInduction i (start * i) m

  powerSeq' : (i : A) → Sequence A
  powerSeq' i = powerSeq i i

  dot : A → ℤn n (lessTransitive (succIsPositive 0) 1<n) → A
  dot 1/n^i x = fromN (ℤn.x {n} {lessTransitive (succIsPositive 0) 1<n} x) * 1/n^i

  dotWellDefined : {x y : A} {b : ℤn n (lessTransitive (succIsPositive 0) 1<n)} → (x ∼ y) → dot x b ∼ dot y b
  dotWellDefined eq = *WellDefined reflexive eq

  sequenceEntries : (b : A) → (b * fromN n ∼ 1R) → Sequence (ℤn n (lessTransitive (succIsPositive 0) 1<n)) → Sequence A
  sequenceEntries 1/n pr1/n s = apply dot (powerSeq' 1/n) s

private
  partialSums' : A → Sequence A → Sequence A
  Sequence.head (partialSums' a seq) = a + Sequence.head seq
  Sequence.tail (partialSums' a seq) = partialSums' (a + Sequence.head seq) (Sequence.tail seq)

  partialSums'WellDefined : (a b : A) → (a ∼ b) → (s : Sequence A) → (m : ℕ) → (index (partialSums' a s) m) ∼ (index (partialSums' b s) m)
  partialSums'WellDefined a b a=b s zero = +WellDefined a=b reflexive
  partialSums'WellDefined a b a=b s (succ m) = partialSums'WellDefined (a + Sequence.head s) (b + Sequence.head s) (+WellDefined a=b reflexive) (Sequence.tail s) m

  partialSums'WellDefined' : (a : A) → (s1 s2 : Sequence A) → (equal : (m : ℕ) → index s1 m ∼ index s2 m) → (m : ℕ) → (index (partialSums' a s1) m) ∼ (index (partialSums' a s2) m)
  partialSums'WellDefined' a s1 s2 equal zero = +WellDefined reflexive (equal 0)
  partialSums'WellDefined' a s1 s2 equal (succ m) = transitive (partialSums'WellDefined (a + Sequence.head s1) (a + Sequence.head s2) (+WellDefined reflexive (equal 0)) _ m) (partialSums'WellDefined' (a + Sequence.head s2) (Sequence.tail s1) (Sequence.tail s2) (λ m → equal (succ m)) m)

  partialSums'Translate : (a b : A) → (s : Sequence A) → (m : ℕ) → (index (partialSums' (a + b) s) m) ∼ (b + index (partialSums' a s) m)
  partialSums'Translate a b s zero = transitive (+WellDefined groupIsAbelian reflexive) (symmetric +Associative)
  partialSums'Translate a b s (succ m) = transitive (partialSums'WellDefined _ _ (transitive (symmetric +Associative) (transitive (+WellDefined reflexive groupIsAbelian) +Associative)) (Sequence.tail s) m) (partialSums'Translate (a + Sequence.head s) b (Sequence.tail s) m)

  powerSeqWellDefined : {a b start1 start2 : A} → (a ∼ b) → (start1 ∼ start2) → (m : ℕ) → (index (powerSeq a start1) m) ∼ (index (powerSeq b start2) m)
  powerSeqWellDefined {a} {b} {s1} {s2} a=b s1=s2 zero = s1=s2
  powerSeqWellDefined {a} {b} {s1} {s2} a=b s1=s2 (succ m) = powerSeqWellDefined a=b (*WellDefined s1=s2 a=b) m

  powerSeqMove : (a start : A) (m : ℕ) → index (powerSeq a (a * start)) m ∼ a * index (powerSeq a start) m
  powerSeqMove a start zero = reflexive
  powerSeqMove a start (succ m) = transitive (powerSeqWellDefined reflexive (transitive *Commutative (*WellDefined reflexive *Commutative)) m) (powerSeqMove _ _ m)

  partialSumsConst : (r s : A) → (m : ℕ) → index (partialSums' r (constSequence s)) m ∼ (r + (s * fromN (succ m)))
  partialSumsConst r s zero = +WellDefined reflexive (transitive (symmetric identIsIdent) (transitive *Commutative (*WellDefined reflexive (symmetric identRight))))
  partialSumsConst r s (succ m) = transitive (partialSumsConst (r + s) s m) (transitive (symmetric +Associative) (+WellDefined reflexive (transitive (+WellDefined (symmetric (transitive *Commutative identIsIdent)) reflexive) (symmetric *DistributesOver+))))

  applyWellDefined : {b : _} {B : Set b} (r1 r2 : Sequence A) (s : Sequence B) → (f : A → B → A) → ({x y : A} {b : B} → (x ∼ y) → f x b ∼ f y b) → ((m : ℕ) → index r1 m ∼ index r2 m) → (m : ℕ) → index (apply f r1 s) m ∼ index (apply f r2 s) m
  applyWellDefined r1 r2 s f wd eq zero = wd (eq 0)
  applyWellDefined r1 r2 s f wd eq (succ m) = applyWellDefined _ _ (Sequence.tail s) f wd (λ n → eq (succ n)) m

partialSums : Sequence A → Sequence A
partialSums = partialSums' 0R

approximations : (b : A) → (b * (fromN n) ∼ 1R) → Sequence (ℤn n (lessTransitive (succIsPositive 0) 1<n)) → Sequence A
approximations 1/n pr1/n s = partialSums (sequenceEntries 1/n pr1/n s)

private
  multiplyZeroSequence : (s : Sequence A) (m : ℕ) → index (apply dot s (constSequence (record { x = 0 ; xLess = lessTransitive (succIsPositive 0) 1<n }))) m ∼ 0R
  multiplyZeroSequence s zero = timesZero'
  multiplyZeroSequence s (succ m) = multiplyZeroSequence _ m

  lemma1 : (x y : A) (s : Sequence (ℤn n (lessTransitive (succIsPositive 0) 1<n))) → (m : ℕ) → index (apply dot (powerSeq x (y * x)) s) m ∼ x * (index (apply dot (powerSeq x y) s) m)
  lemma1 x y s zero = transitive *Associative *Commutative
  lemma1 x y s (succ m) = lemma1 x (y * x) (Sequence.tail s) m

  lemma2 : (w x y z : A) (s : Sequence (ℤn n (lessTransitive (succIsPositive 0) 1<n))) → (m : ℕ) → (w * index (partialSums' x (apply dot (powerSeq y z) s)) m) ∼ index (partialSums' (w * x) (apply dot (powerSeq y (z * w)) s)) m
  lemma2 x y z w s zero = transitive *DistributesOver+ (+WellDefined reflexive (transitive (transitive (*WellDefined reflexive *Commutative) (transitive *Associative (*WellDefined *Commutative reflexive))) *Commutative))
  lemma2 x y z w s (succ m) = transitive (lemma2 x (y + dot w (Sequence.head s)) z (w * z) (Sequence.tail s) m) (transitive (partialSums'WellDefined _ (_ + dot (w * x) (Sequence.head s)) (transitive *DistributesOver+ (+WellDefined reflexive (transitive *Commutative (symmetric *Associative)))) _ m) (partialSums'WellDefined' _ _ _ (λ n → applyWellDefined (powerSeq z ((w * z) * x)) (powerSeq z ((w * x) * z)) (Sequence.tail s) dot (λ {m} {n} {s} m=n → dotWellDefined {m} {n} {s} m=n) (λ n → powerSeqWellDefined reflexive (transitive (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative)) *Associative) n) n) m))

approximationComesFromBelow : (1/n : A) → (1/nPr : 1/n * (fromN n) ∼ 1R) → (a : A) → (0<a : 0R < a) → (a<1 : a < 1R) → (m : ℕ) → index (approximations 1/n 1/nPr (baseNExpansion a 0<a a<1)) m <= a
approximationComesFromBelow 1/n 1/nPr a 0<a a<1 zero with computeFloor' 0 (Semiring.sumZeroRight ℕSemiring n) (a * fromN n) (0<aFromN 0<a) ((<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1)))
... | x , record { prBelow = inl prBelow ; prAbove = prAbove } = inl (<WellDefined (symmetric identLeft) reflexive (ringCanCancelPositive (0<n prBelow) (<WellDefined (transitive (symmetric identIsIdent) (transitive *Commutative (transitive (*WellDefined reflexive (symmetric 1/nPr)) *Associative))) reflexive prBelow)))
... | x , record { prBelow = inr prBelow ; prAbove = prAbove } = inr (transitive identLeft (transitive (transitive (transitive (transitive (*WellDefined prBelow reflexive) (transitive (symmetric *Associative) (*WellDefined reflexive *Commutative))) (*WellDefined reflexive 1/nPr)) (*Commutative)) identIsIdent))
approximationComesFromBelow 1/n 1/nPr a 0<a a<1 (succ m) with computeFloor' 0 (Semiring.sumZeroRight ℕSemiring n) (a * fromN n) (0<aFromN 0<a) ((<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1)))
... | x , record { prBelow = inr x=an ; prAbove = an<x+1 } = inr (transitive (partialSums'Translate 0G _ _ m) (transitive (+WellDefined (transitive (*WellDefined x=an reflexive) (transitive (symmetric *Associative) (*WellDefined reflexive (transitive *Commutative 1/nPr)))) reflexive) (transitive (+WellDefined (transitive *Commutative identIsIdent) (transitive (partialSums'WellDefined' 0G _ (constSequence 0G) (λ m → transitive (multiplyZeroSequence (powerSeq 1/n (1/n * 1/n)) m) (identityOfIndiscernablesRight _∼_ reflexive (equalityCommutative (indexAndConst 0G m)))) m) (transitive (partialSumsConst _ _ m) (transitive identLeft timesZero')))) identRight)))
... | x , record { prBelow = inl x<an ; prAbove = an<x+1 } with approximationComesFromBelow 1/n 1/nPr ((a * fromN n) + inverse (fromN x)) (moveInequality x<an) (<WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) (orderRespectsAddition an<x+1 (inverse (fromN x)))) m
... | inl inter<an = inl (<WellDefined (symmetric (partialSums'Translate 0G (fromN x * 1/n) _ m)) reflexive (<WellDefined (+WellDefined reflexive (symmetric (partialSums'WellDefined 0G (fromN n * 0G) (symmetric timesZero) _ m))) reflexive (ringCanCancelPositive (0<n an<x+1) (<WellDefined (symmetric (transitive *DistributesOver+' (+WellDefined (transitive (symmetric *Associative) (transitive (*WellDefined reflexive 1/nPr) (transitive *Commutative identIsIdent))) (transitive *Commutative (transitive (lemma2 (fromN n) (fromN n * 0G) 1/n (1/n * 1/n) _ m) (transitive (partialSums'WellDefined _ 0G (transitive (*WellDefined reflexive timesZero) timesZero) _ m) (partialSums'WellDefined' 0G _ _ (λ m → applyWellDefined _ _ _ dot (λ {x} {y} {s} → dotWellDefined {x} {y} {s}) (λ m → powerSeqWellDefined {_} {1/n} {_} {1/n} reflexive (transitive (symmetric *Associative) (transitive (transitive *Commutative (*WellDefined 1/nPr reflexive)) identIsIdent)) m) m) m))))))) reflexive (<WellDefined groupIsAbelian (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)) (orderRespectsAddition inter<an (fromN x)))))))
... | inr inter=an = inr (transitive (partialSums'Translate 0G (fromN x * 1/n) _ m) (cancelIntDom' (isIntDom λ t → anyComparisonImpliesNontrivial a<1 (symmetric t)) ans λ t → irreflexive (<WellDefined reflexive t (fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial a<1)) (lessTransitive (succIsPositive 0) 1<n)))))
  where
    ans : (((fromN x * 1/n) + index (partialSums' 0G (apply dot (powerSeq 1/n (1/n * 1/n)) (baseNExpansion ((a * fromN n) + inverse (fromN x)) (moveInequality x<an) (<WellDefined reflexive (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invRight) identRight)) (orderRespectsAddition an<x+1 (inverse (fromN x))))))) m) * fromN n) ∼ a * fromN n
    ans = transitive (transitive *DistributesOver+' (+WellDefined (transitive (symmetric *Associative) (transitive (*WellDefined reflexive 1/nPr) (transitive *Commutative identIsIdent))) *Commutative)) (transitive (+WellDefined reflexive (transitive (lemma2 (fromN n) 0G 1/n (1/n * 1/n) _ m) (transitive (partialSums'WellDefined _ _ timesZero _ m) (partialSums'WellDefined' _ _ _ (λ m → applyWellDefined _ _ _ dot (λ {x} {y} {s} → dotWellDefined {x} {y} {s}) (λ m → powerSeqWellDefined reflexive (transitive (symmetric *Associative) (transitive (*WellDefined reflexive 1/nPr) (transitive *Commutative identIsIdent))) m) m) m)))) (transitive (+WellDefined reflexive inter=an) (transitive groupIsAbelian (transitive (symmetric +Associative) (transitive (+WellDefined reflexive invLeft) identRight)))))

pow : ℕ → A → A
pow zero x = 1R
pow (succ n) x = x * pow n x

powPos : (m : ℕ) {a : A} → (0R < a) → 0R < pow m a
powPos zero 0<a = 0<1 (anyComparisonImpliesNontrivial 0<a)
powPos (succ m) 0<a = orderRespectsMultiplication 0<a (powPos m 0<a)

approximationIsNear : (1/n : A) → (1/nPr : 1/n * (fromN n) ∼ 1R) → (a : A) → (0<a : 0R < a) → (a<1 : a < 1R) → (m : ℕ) → a < ((index (approximations 1/n 1/nPr (baseNExpansion a 0<a a<1)) m) + pow m 1/n)
approximationIsNear 1/n 1/npr a 0<a a<1 zero with computeFloor' 0 (Semiring.sumZeroRight ℕSemiring n) (a * fromN n) (0<aFromN 0<a) (<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1))
... | x , record { prBelow = inl prBelow ; prAbove = prAbove } = <WellDefined reflexive (transitive (symmetric identLeft) +Associative) (ringCanCancelPositive (0<n prAbove) (<Transitive prAbove (<WellDefined reflexive (transitive (+WellDefined (transitive (*WellDefined reflexive (symmetric 1/npr)) *Associative) (symmetric identIsIdent)) (symmetric *DistributesOver+')) (<WellDefined reflexive (transitive groupIsAbelian (+WellDefined (transitive (symmetric identIsIdent) *Commutative) reflexive)) (orderRespectsAddition (<WellDefined identRight reflexive (fromNPreservesOrder (0<1 (anyComparisonImpliesNontrivial prAbove)) 1<n)) (fromN x))))))
... | x , record { prBelow = inr prBelow ; prAbove = prAbove } = <WellDefined reflexive (symmetric (transitive (symmetric +Associative) identLeft)) (ringCanCancelPositive (0<n prAbove) (<WellDefined prBelow (symmetric (transitive *DistributesOver+' (+WellDefined (transitive (symmetric *Associative) (transitive *Commutative (transitive (*WellDefined 1/npr reflexive) identIsIdent))) identIsIdent))) (<WellDefined identLeft groupIsAbelian (orderRespectsAddition (0<n prAbove) (fromN x)))))
approximationIsNear 1/n 1/npr a 0<a a<1 (succ m) with computeFloor' 0 (Semiring.sumZeroRight ℕSemiring n) (a * fromN n) (0<aFromN 0<a) (<WellDefined reflexive identIsIdent (ringCanMultiplyByPositive (0<n 0<a) a<1))
... | x , record { prBelow = inl prBelow ; prAbove = prAbove } = <WellDefined reflexive (+WellDefined (symmetric (partialSums'Translate 0G (fromN x * 1/n) _ m)) reflexive) (ringCanCancelPositive (0<n prAbove) (<WellDefined reflexive (transitive (+WellDefined (transitive (+WellDefined (transitive (transitive (symmetric identIsIdent) (transitive *Commutative (*WellDefined reflexive (symmetric 1/npr))) ) *Associative) *Commutative) (symmetric *DistributesOver+')) (transitive (transitive (transitive (symmetric identIsIdent) (*WellDefined (transitive (symmetric 1/npr) *Commutative) reflexive)) (symmetric *Associative)) *Commutative)) (symmetric *DistributesOver+')) (<WellDefined reflexive (+WellDefined (+WellDefined reflexive (transitive (partialSums'WellDefined' _ _ _ (λ m → applyWellDefined _ _ _ dot (λ {_} {_} {s} → dotWellDefined {_} {_} {s}) (λ m → powerSeqWellDefined reflexive (transitive (transitive (transitive (symmetric identIsIdent) *Commutative) (*WellDefined reflexive (symmetric 1/npr))) *Associative) m) m) m) (symmetric (lemma2 (fromN n) 0G 1/n (1/n * 1/n) _ m)))) reflexive) (<WellDefined reflexive (+WellDefined (+WellDefined reflexive (partialSums'WellDefined _ _ (symmetric timesZero) _ m)) reflexive) (<WellDefined reflexive +Associative u)))))
  where
    t : ((a * fromN n) + inverse (fromN x)) < ((index (partialSums' 0R (apply dot (powerSeq 1/n 1/n) (baseNExpansion ((a * fromN n) + inverse (fromN x)) (moveInequality prBelow) _))) m) + pow m 1/n)
    t = approximationIsNear 1/n 1/npr ((a * fromN n) + inverse (fromN x)) (moveInequality prBelow) (<WellDefined reflexive (transitive (transitive (symmetric +Associative) (+WellDefined reflexive invRight)) identRight) (orderRespectsAddition prAbove (inverse (fromN x)))) m
    u : (a * fromN n) < (fromN x + ((index (partialSums' 0R (apply dot (powerSeq 1/n 1/n) (baseNExpansion ((a * fromN n) + inverse (fromN x)) (moveInequality prBelow) _))) m) + pow m 1/n))
    u = <WellDefined (transitive (transitive (symmetric +Associative) (+WellDefined reflexive invLeft)) identRight) groupIsAbelian (orderRespectsAddition t (fromN x))
... | x , record { prBelow = inr prBelow ; prAbove = prAbove } = <WellDefined reflexive (+WellDefined (symmetric (partialSums'Translate 0G (fromN x * 1/n) _ m)) reflexive) (ringCanCancelPositive (0<n prAbove) (<WellDefined reflexive (transitive (+WellDefined (transitive (+WellDefined (transitive (transitive (symmetric identIsIdent) (transitive *Commutative (*WellDefined reflexive (symmetric 1/npr))) ) *Associative) *Commutative) (symmetric *DistributesOver+')) (transitive (transitive (transitive (symmetric identIsIdent) (*WellDefined (transitive (symmetric 1/npr) *Commutative) reflexive)) (symmetric *Associative)) *Commutative)) (symmetric *DistributesOver+')) (<WellDefined reflexive (+WellDefined (+WellDefined reflexive (transitive (partialSums'WellDefined' _ _ _ (λ m → applyWellDefined _ _ _ dot (λ {_} {_} {s} → dotWellDefined {_} {_} {s}) (λ m → powerSeqWellDefined reflexive (transitive (transitive (transitive (symmetric identIsIdent) *Commutative) (*WellDefined reflexive (symmetric 1/npr))) *Associative) m) m) m) (symmetric (lemma2 (fromN n) 0G 1/n (1/n * 1/n) _ m)))) reflexive) (<WellDefined reflexive (+WellDefined (+WellDefined reflexive (partialSums'WellDefined _ _ (symmetric timesZero) _ m)) reflexive) (<WellDefined reflexive +Associative (<WellDefined (transitive identLeft prBelow) groupIsAbelian (orderRespectsAddition (<WellDefined reflexive (transitive (symmetric identLeft) (+WellDefined (symmetric (transitive (partialSums'WellDefined' 0R _ (constSequence 0R) (λ m → transitive (multiplyZeroSequence _ m) (identityOfIndiscernablesLeft _∼_ reflexive (indexAndConst 0G m))) m ) (transitive (partialSumsConst _ _ m) (transitive identLeft timesZero')))) reflexive)) (powPos m {1/n} (reciprocalPositive _ _ (0<n 0<a) (transitive *Commutative 1/npr)))) (fromN x))))))))
