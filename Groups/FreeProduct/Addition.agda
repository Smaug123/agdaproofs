{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Functions.Definition
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Setoids.Setoids
open import Groups.Definition
open import LogicalFormulae
open import Orders.WellFounded.Definition
open import Numbers.Naturals.Semiring
open import Groups.Lemmas

module Groups.FreeProduct.Addition {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) {a b : _} {A : I → Set a} {S : (i : I) → Setoid {a} {b} (A i)} {_+_ : (i : I) → (A i) → (A i) → A i} (decidableGroups : (i : I) → (x y : A i) → ((Setoid._∼_ (S i) x y)) || ((Setoid._∼_ (S i) x y) → False)) (G : (i : I) → Group (S i) (_+_ i)) where

open import Groups.FreeProduct.Definition decidableIndex decidableGroups G
open import Groups.FreeProduct.Setoid decidableIndex decidableGroups G

prependEqual : (i : I) (g : A i) .(nonZero : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → (j : I) → i ≡ j → (w : ReducedSequenceBeginningWith j) → ReducedSequence
prependEqual i g nonzero .i refl (ofEmpty .i h nonZero) with decidableGroups i (_+_ i g h) (Group.0G (G i))
prependEqual i g nonzero .i refl (ofEmpty .i h nonZero) | inl sumZero = empty
prependEqual i g nonzero .i refl (ofEmpty .i h nonZero) | inr sumNotZero = nonempty i (ofEmpty i (_+_ i g h) sumNotZero)
prependEqual i g nonzero .i refl (prependLetter .i h nonZero x x₁) with decidableGroups i (_+_ i g h) (Group.0G (G i))
prependEqual i g nonzero .i refl (prependLetter .i h nonZero {j} x x₁) | inl sumZero = nonempty j x
prependEqual i g nonzero .i refl (prependLetter .i h nonZero x pr) | inr sumNotZero = nonempty i (prependLetter i (_+_ i g h) sumNotZero x pr)

prepend : (i : I) → (g : A i) → .(nonZero : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → ReducedSequence → ReducedSequence
prepend i g nonzero empty = nonempty i (ofEmpty i g nonzero)
prepend i g nonzero (nonempty j x) with decidableIndex i j
prepend i g nonzero (nonempty j w) | inl i=j = prependEqual i g nonzero j i=j w
prepend i g nonzero (nonempty j x) | inr i!=j = nonempty i (prependLetter i g nonzero x i!=j)

plus' : {j : _} → (ReducedSequenceBeginningWith j) → ReducedSequence → ReducedSequence
plus' (ofEmpty i g nonZero) s = prepend i g nonZero s
plus' (prependLetter i g nonZero x pr) s = prepend i g nonZero (plus' x s)

_+RP_ : ReducedSequence → ReducedSequence → ReducedSequence

empty +RP b = b
nonempty i x +RP b = plus' x b

abstract
  prependWD : {i : I} → (g1 g2 : A i) → .(nz1 : _) → .(nz2 : _) → (y : ReducedSequence) (eq : Setoid._∼_ (S i) g1 g2) → prepend i g1 nz1 y =RP prepend i g2 nz2 y
  prependWD {i} g1 g2 nz1 nz2 empty g1=g2 with decidableIndex i i
  prependWD {i} g1 g2 nz1 nz2 empty g1=g2 | inl refl = g1=g2
  prependWD {i} g1 g2 nz1 nz2 empty g1=g2 | inr x = exFalso (x refl)
  prependWD {i} g1 g2 nz1 nz2 (nonempty j x) g1=g2 with decidableIndex i j
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl with decidableGroups j ((j + g1) g) (Group.0G (G j))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inl x with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inl x | inl x₁ = record {}
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inl x | inr bad = exFalso (bad (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.symmetric (Setoid.eq (S j)) g1=g2) (Equivalence.reflexive (Setoid.eq (S j)))) x))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inr x with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inr bad | inl p = exFalso (bad (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) g1=g2 (Equivalence.reflexive (Setoid.eq (S j)))) p))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inr x | inr x₁ with decidableIndex j j
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inr x | inr x₁ | inl refl = Group.+WellDefined (G j) g1=g2 (Equivalence.reflexive (Setoid.eq (S j)))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (ofEmpty .j g nonZero)) g1=g2 | inl refl | inr x | inr x₁ | inr bad = exFalso (bad refl)
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl with decidableGroups j ((j + g1) g) (Group.0G (G j))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inl x with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inl x | inl x₂ = =RP'reflex w
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inl x | inr bad = exFalso (bad (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.symmetric (Setoid.eq (S j)) g1=g2) (Equivalence.reflexive (Setoid.eq (S j)))) x))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inr neq with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inr neq | inl x = exFalso (neq (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) g1=g2 (Equivalence.reflexive (Setoid.eq (S j)))) x))
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inr neq | inr x with decidableIndex j j
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inr neq | inr x | inl refl = Group.+WellDefined (G j) g1=g2 (Equivalence.reflexive (Setoid.eq (S j))) ,, =RP'reflex w
  prependWD {.j} g1 g2 nz1 nz2 (nonempty j (prependLetter .j g nonZero w x₁)) g1=g2 | inl refl | inr neq | inr x | inr bad = exFalso (bad refl)
  prependWD {i} g1 g2 nz1 nz2 (nonempty j x) g1=g2 | inr i!=j with decidableIndex i i
  prependWD {i} g1 g2 nz1 nz2 (nonempty j x) g1=g2 | inr i!=j | inl refl = g1=g2 ,, =RP'reflex x
  prependWD {i} g1 g2 nz1 nz2 (nonempty j x) g1=g2 | inr i!=j | inr bad = exFalso (bad refl)

abstract
  prependWD' : {i : I} → (g : A i) → .(nz : _) → (y1 y2 : ReducedSequence) (eq : y1 =RP y2) → prepend i g nz y1 =RP prepend i g nz y2
  prependWD' {i} g1 nz empty empty eq with decidableIndex i i
  prependWD' {i} g1 nz empty empty eq | inl refl = Equivalence.reflexive (Setoid.eq (S i))
  prependWD' {i} g1 nz empty empty eq | inr x = exFalso (x refl)
  prependWD' {i} g1 nz (nonempty j x) (nonempty k x₁) eq with decidableIndex i j
  prependWD' {.j} g1 nz (nonempty j w1) (nonempty k w2) eq | inl refl with decidableIndex j k
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl with decidableGroups j ((j + g1) g) (Group.0G (G j))
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inl eq1 with decidableGroups j ((j + g1) h) (Group.0G (G j))
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inl eq1 | inl x = record {}
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inl eq1 | inr x with decidableIndex j j
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inl eq1 | inr x | inl refl = exFalso (x (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (Equivalence.symmetric (Setoid.eq (S j)) eq)) eq1))
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inr neq1 with decidableGroups j ((j + g1) h) (Group.0G (G j))
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inr neq1 | inl x with decidableIndex j j
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inr neq1 | inl x | inl refl = exFalso (neq1 (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) eq) x))
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inr neq1 | inr x with decidableIndex j j
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty .j (ofEmpty .j h nonZero₁)) eq | inl refl | inl refl | inr neq1 | inr x | inl refl = Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) eq
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl with decidableIndex j j
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl with decidableGroups j ((j + g1) g) (Group.0G (G j))
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inl eq1 with decidableGroups j ((j + g1) h) (Group.0G (G j))
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inl eq1 | inl eq2 = _&&_.snd eq
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inl eq1 | inr neq2 = exFalso (neq2 (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (Equivalence.symmetric (Setoid.eq (S j)) (_&&_.fst eq))) eq1))
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inr neq1 with decidableGroups j ((j + g1) h) (Group.0G (G j))
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inr neq1 | inl eq2 = exFalso (neq1 (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (_&&_.fst eq)) eq2))
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inr neq1 | inr _ with decidableIndex j j
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inr neq1 | inr _ | inl refl = Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (_&&_.fst eq) ,, _&&_.snd eq
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty .j (prependLetter .j h nonZero₁ w2 x₁)) eq | inl refl | inl refl | inl refl | inr neq1 | inr _ | inr bad = exFalso (bad refl)
  prependWD' {.j} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty k (ofEmpty .k g₁ nonZero₁)) eq | inl refl | inr j!=k with decidableIndex j k
  prependWD' {j} g1 nz (nonempty j (ofEmpty j g nonZero)) (nonempty k (ofEmpty .k g₁ nonZero₁)) eq | inl refl | inr j!=k | inl j=k = exFalso (j!=k j=k)
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty k (prependLetter .k g₁ nonZero₁ w2 x₁)) eq | inl refl | inr j!=k with decidableIndex j k
  prependWD' {.j} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty k (prependLetter .k g₁ nonZero₁ w2 x₁)) eq | inl refl | inr j!=k | inl j=k = exFalso (j!=k j=k)
  prependWD' {i} g1 nz (nonempty j w1) (nonempty k w2) eq | inr i!=j with decidableIndex i k
  prependWD' {.k} g1 nz (nonempty j (ofEmpty .j g nonZero)) (nonempty k (ofEmpty .k g₁ nonZero₁)) eq | inr i!=j | inl refl with decidableIndex j k
  prependWD' {.k} g1 nz (nonempty .k (ofEmpty .k g nonZero)) (nonempty k (ofEmpty .k g₁ nonZero₁)) eq | inr i!=j | inl refl | inl refl = exFalso (i!=j refl)
  prependWD' {.k} g1 nz (nonempty j (prependLetter .j g nonZero w1 x)) (nonempty k (prependLetter .k g₁ nonZero₁ w2 x₁)) eq | inr i!=j | inl refl with decidableIndex j k
  prependWD' {.k} g1 nz (nonempty .k (prependLetter .k g nonZero w1 x)) (nonempty k (prependLetter .k g₁ nonZero₁ w2 x₁)) eq | inr i!=j | inl refl | inl refl = exFalso (i!=j refl)
  prependWD' {i} g1 nz (nonempty j w1) (nonempty k w2) eq | inr i!=j | inr i!=k with decidableIndex i i
  prependWD' {i} g1 nz (nonempty j w1) (nonempty k w2) eq | inr i!=j | inr i!=k | inl refl = Equivalence.reflexive (Setoid.eq (S i)) ,, eq
  prependWD' {i} g1 nz (nonempty j w1) (nonempty k w2) eq | inr i!=j | inr i!=k | inr x = exFalso (x refl)

private
  prependLetterWD : {i : I} {h1 h2 : A i} (h1=h2 : Setoid._∼_ (S i) h1 h2) → .(nonZero1 : _) .(nonZero2 : _) {j1 j2 : I} (w1 : ReducedSequenceBeginningWith j1) (w2 : ReducedSequenceBeginningWith j2) → (eq : =RP' w1 w2) → (x1 : i ≡ _ → False) (x2 : i ≡ _ → False) → nonempty i (prependLetter i h1 nonZero1 w1 x1) =RP nonempty i (prependLetter i h2 nonZero2 w2 x2)
  prependLetterWD {i} h1=h2 nonZero1 nonZero2 {j1} {j2} w1 w2 eq x1 x2 with decidableIndex i i
  prependLetterWD {i} h1=h2 nonZero1 nonZero2 {j1} {j2} w1 w2 eq x1 x2 | inl refl = h1=h2 ,, eq
  prependLetterWD {i} h1=h2 nonZero1 nonZero2 {j1} {j2} w1 w2 eq x1 x2 | inr x = exFalso (x refl)

abstract
  plus'WD' : {i : I} (x : ReducedSequenceBeginningWith i) (y1 y2 : ReducedSequence) → (y1 =RP y2) → plus' x y1 =RP plus' x y2
  plus'WD' x empty empty eq = Equivalence.reflexive (Setoid.eq freeProductSetoid) {plus' x empty}
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 w1) (nonempty i2 w2) eq with decidableIndex j i1
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j w1) (nonempty i2 w2) eq | inl refl with decidableIndex j i2
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j g₁ nonZero₁)) (nonempty .j (ofEmpty .j g₂ nonZero₂)) eq | inl refl | inl refl with decidableIndex j j
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl with decidableGroups j ((j + g) h1) (Group.0G (G j))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inl x with decidableGroups j ((j + g) h2) (Group.0G (G j))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inl x | inl x₁ = record {}
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inl x | inr bad = exFalso (bad (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (Equivalence.symmetric (Setoid.eq (S j)) eq)) x))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inr x with decidableGroups j ((j + g) h2) (Group.0G (G j))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inr x | inl bad = exFalso (x (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) eq) bad))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inr x | inr x₁ with decidableIndex j j
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inr x | inr x₁ | inl refl = Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) eq
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j h1 nonZero₁)) (nonempty .j (ofEmpty .j h2 nonZero₂)) eq | inl refl | inl refl | inl refl | inr x | inr x₁ | inr bad = exFalso (bad refl)
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl with decidableGroups j ((j + g) h1) (Group.0G (G j))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl | inl eq1 with decidableGroups j ((j + g) h2) (Group.0G (G j))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl | inl eq1 | inl x₂ with decidableIndex j j
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl | inl eq1 | inl x₂ | inl refl = _&&_.snd eq
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl | inl eq1 | inr neq2 with decidableIndex j j
  ... | inl refl = exFalso (neq2 (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (Equivalence.symmetric (Setoid.eq (S j)) (_&&_.fst eq))) eq1))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl | inr neq1 with decidableGroups j ((j + g) h2) (Group.0G (G j))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl | inr neq1 | inl eq2 with decidableIndex j j
  ... | inl refl = exFalso (neq1 (Equivalence.transitive (Setoid.eq (S j)) (Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (_&&_.fst eq)) eq2))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j h1 nonZero₁ w1 x)) (nonempty .j (prependLetter .j h2 nonZero₂ w2 x₁)) eq | inl refl | inl refl | inr neq1 | inr x₂ with decidableIndex j j
  ... | inl refl = Group.+WellDefined (G j) (Equivalence.reflexive (Setoid.eq (S j))) (_&&_.fst eq) ,, _&&_.snd eq
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j g₁ nonZero₁)) (nonempty i2 (ofEmpty .i2 g₂ nonZero₂)) eq | inl refl | inr x with decidableIndex j i2
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (ofEmpty .j g₁ nonZero₁)) (nonempty .j (ofEmpty .j g₂ nonZero₂)) eq | inl refl | inr x | inl refl = exFalso (x refl)
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty .j (prependLetter .j g₁ nonZero₁ w1 x₁)) (nonempty i2 (prependLetter .i2 g₂ nonZero₂ w2 x₂)) eq | inl refl | inr x with decidableIndex j i2
  plus'WD' {.i2} (ofEmpty .i2 g nonZero) (nonempty .i2 (prependLetter .i2 g₁ nonZero₁ w1 x₁)) (nonempty i2 (prependLetter .i2 g₂ nonZero₂ w2 x₂)) eq | inl refl | inr x | inl refl = exFalso (x refl)
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 w1) (nonempty i2 w2) eq | inr j!=i1 with decidableIndex j i2
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 (ofEmpty .i1 g₁ nonZero₁)) (nonempty .j (ofEmpty .j g₂ nonZero₂)) eq | inr j!=i1 | inl refl with decidableIndex i1 j
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 (ofEmpty .i1 g₁ nonZero₁)) (nonempty .j (ofEmpty .j g₂ nonZero₂)) eq | inr j!=i1 | inl refl | inl x = exFalso (j!=i1 (equalityCommutative x))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 (prependLetter .i1 g₁ nonZero₁ w1 x)) (nonempty .j (prependLetter .j g₂ nonZero₂ w2 x₁)) eq | inr j!=i1 | inl refl with decidableIndex i1 j
  ... | inl bad = exFalso (j!=i1 (equalityCommutative bad))
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 w1) (nonempty i2 w2) eq | inr j!=i1 | inr j!=i2 with decidableIndex j j
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 w1) (nonempty i2 w2) eq | inr j!=i1 | inr j!=i2 | inl refl = Equivalence.reflexive (Setoid.eq (S j)) ,, eq
  plus'WD' {j} (ofEmpty j g nonZero) (nonempty i1 w1) (nonempty i2 w2) eq | inr j!=i1 | inr j!=i2 | inr x = exFalso (x refl)
  plus'WD' {j} (prependLetter j g nonZero l x) (nonempty i (ofEmpty .i h1 nonZero1)) (nonempty i2 (ofEmpty .i2 h2 nonZero2)) eq with decidableIndex i i2
  ... | inl refl = prependWD' g nonZero (plus' l (nonempty i (ofEmpty i h1 nonZero1))) (plus' l (nonempty i2 (ofEmpty i2 h2 nonZero2))) (plus'WD' l (nonempty i2 (ofEmpty i2 h1 nonZero1)) (nonempty i2 (ofEmpty i2 h2 nonZero2)) t)
    where
      t : =RP' (ofEmpty i2 h1 nonZero1) (ofEmpty i2 h2 nonZero2)
      t with decidableIndex i2 i2
      t | inl refl = eq
      t | inr x = exFalso (x refl)
  ... | inr i!=i2 = exFalso' eq
  plus'WD' {j} (prependLetter j g nonZero l x) (nonempty i (prependLetter .i g₁ nonZero₁ w1 x₁)) (nonempty i2 (prependLetter .i2 g₂ nonZero₂ w2 x₂)) eq with decidableIndex i i2
  plus'WD' {j} (prependLetter j g nonZero l x) (nonempty i (prependLetter .i h1 nonZero1 w1 x1)) (nonempty .i (prependLetter .i h2 nonZero2 w2 x2)) eq | inl refl = prependWD' g nonZero (plus' l (nonempty i (prependLetter i h1 nonZero1 w1 x1))) (plus' l (nonempty i (prependLetter i h2 nonZero2 w2 x2))) (plus'WD' l (nonempty i (prependLetter i h1 nonZero1 w1 x1)) (nonempty i (prependLetter i h2 nonZero2 w2 x2)) (prependLetterWD (_&&_.fst eq) nonZero1 nonZero2 w1 w2 (_&&_.snd eq) x1 x2))

abstract
  plusEmptyRight : {i : I} (x : ReducedSequenceBeginningWith i) → _=RP_ (plus' x empty) (nonempty i x)
  plusEmptyRight (ofEmpty i g nonZero) with decidableIndex i i
  plusEmptyRight (ofEmpty i g nonZero) | inl refl = Equivalence.reflexive (Setoid.eq (S i))
  plusEmptyRight (ofEmpty i g nonZero) | inr x = exFalso (x refl)
  plusEmptyRight (prependLetter i g nonZero {j} x i!=j) with plusEmptyRight x
  ... | b with plus' x empty
  plusEmptyRight (prependLetter i g nonZero {j} x i!=j) | b | nonempty k w with decidableIndex i k
  plusEmptyRight (prependLetter .k g nonZero {j} x i!=j) | b | nonempty k (ofEmpty .k h nonZero₁) | inl refl with decidableGroups k ((k + g) h) (Group.0G (G k))
  plusEmptyRight (prependLetter .k g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty k (ofEmpty .k h nonZero₁) | inl refl | inl g+k=hinv with decidableIndex k i
  plusEmptyRight (prependLetter .i g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty .i (ofEmpty .i h nonZero₁) | inl refl | inl g+k=hinv | inl refl = exFalso (i!=j refl)
  plusEmptyRight (prependLetter .k g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty k (ofEmpty .k h nonZero₁) | inl refl | inr x₁ with decidableIndex k i
  plusEmptyRight (prependLetter .i g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty .i (ofEmpty .i h nonZero₁) | inl refl | inr x₁ | inl refl = exFalso (i!=j refl)
  plusEmptyRight (prependLetter .k g nonZero {j} w1 i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl with decidableGroups k ((k + g) h) (Group.0G (G k))
  plusEmptyRight (prependLetter .k g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inl p with decidableIndex k i
  plusEmptyRight (prependLetter .i g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty .i (prependLetter .i h nonZero₁ w x₁) | inl refl | inl p | inl refl = exFalso (i!=j refl)
  plusEmptyRight (prependLetter .k g nonZero {j} w1 i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inr x₂ with decidableIndex k k
  plusEmptyRight (prependLetter .k g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inr x₂ | inl refl with decidableIndex k i
  plusEmptyRight (prependLetter .i g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty .i (prependLetter .i h nonZero₁ w x₁) | inl refl | inr x₂ | inl refl | inl refl = exFalso (i!=j refl)
  plusEmptyRight (prependLetter .k g nonZero {j} w1 i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inr x₂ | inr x = exFalso (x refl)
  plusEmptyRight (prependLetter i g nonZero {j} w1 i!=j) | b | nonempty k w | inr i!=k with decidableIndex i i
  plusEmptyRight (prependLetter i g nonZero {j} w1 i!=j) | b | nonempty k w | inr i!=k | inl refl = Equivalence.reflexive (Setoid.eq (S i)) ,, b
  plusEmptyRight (prependLetter i g nonZero {j} w1 i!=j) | b | nonempty k w | inr i!=k | inr x = exFalso (x refl)

abstract
  prependFrom : {i : I} (g1 g2 : A i) (pr : (Setoid._∼_ (S i) (_+_ i g1 g2) (Group.0G (G i))) → False) (c : ReducedSequence) .(p2 : _) .(p3 : _) → prepend i (_+_ i g1 g2) pr c =RP prepend i g1 p2 (prepend i g2 p3 c)
  prependFrom {i} g1 g2 pr empty _ _ with decidableIndex i i
  prependFrom {i} g1 g2 pr empty _ _ | inl refl with decidableGroups i ((i + g1) g2) (Group.0G (G i))
  prependFrom {i} g1 g2 pr empty _ _ | inl refl | inl bad = exFalso (pr bad)
  prependFrom {i} g1 g2 pr empty _ _ | inl refl | inr _ with decidableIndex i i
  prependFrom {i} g1 g2 pr empty _ _ | inl refl | inr _ | inl refl = Equivalence.reflexive (Setoid.eq (S i))
  prependFrom {i} g1 g2 pr empty _ _ | inl refl | inr _ | inr bad = exFalso (bad refl)
  prependFrom {i} g1 g2 pr empty _ _ | inr bad = exFalso (bad refl)
  prependFrom {i} g1 g2 pr (nonempty j x) _ _ with decidableIndex i j
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl with decidableGroups j ((j + (j + g1) g2) g) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inl eq with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) g1Nonzero _ | inl refl | inl eq3 | inl eq2 = exFalso (g1Nonzero t)
    where
      open Setoid (S j)
      open Group (G j)
      open Equivalence eq
      t : g1 ∼ 0G
      t = transitive (symmetric identRight) (transitive (+WellDefined reflexive (symmetric eq2)) (transitive +Associative eq3))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inl eq | inr neq with decidableIndex j j
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inl eq | inr neq | inl refl with decidableGroups j ((j + g1) ((j + g2) g)) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inl eq | inr neq | inl refl | inl eq2 = record {}
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inl eq | inr neq | inl refl | inr neq2 = exFalso (neq2 (Equivalence.transitive (Setoid.eq (S j)) (Group.+Associative (G j)) eq))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inl eq | inr neq | inr bad = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inl eq2 with decidableIndex j j
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inl eq2 | inl refl = transitive (symmetric +Associative) (transitive (+WellDefined reflexive eq2) identRight)
    where
      open Setoid (S j)
      open Group (G j)
      open Equivalence eq
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inl eq2 | inr bad = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inr neq2 with decidableIndex j j
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inr neq2 | inl refl with decidableGroups j ((j + g1) ((j + g2) g)) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inr neq2 | inl refl | inl eq2 = exFalso (neq (Equivalence.transitive (Setoid.eq (S j)) (Equivalence.symmetric (Setoid.eq (S j)) (Group.+Associative (G j))) eq2))
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inr neq2 | inl refl | inr neq3 with decidableIndex j j
  ... | inl refl = Equivalence.symmetric (Setoid.eq (S j)) (Group.+Associative (G j))
  ... | inr bad = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (ofEmpty j g nonZero)) _ _ | inl refl | inr neq | inr neq2 | inr bad = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl with decidableGroups j ((j + (j + g1) g2) g) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inl eq1 with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero {k} x x₁)) p2 _ | inl refl | inl eq1 | inl eq2 = exFalso (p2 (transitive (transitive (symmetric identRight) (transitive (+WellDefined reflexive (symmetric eq2)) +Associative)) eq1))
    where
      open Setoid (S j)
      open Group (G j)
      open Equivalence eq
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inl eq1 | inr neq with decidableIndex j j
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inl eq1 | inr neq | inl refl with decidableGroups j ((j + g1) ((j + g2) g)) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inl eq1 | inr neq | inl refl | inl eq2 = =RP'reflex x
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inl eq1 | inr neq | inl refl | inr neq2 = exFalso (neq2 (Equivalence.transitive (Setoid.eq (S j)) (Group.+Associative (G j)) eq1))
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inl eq1 | inr neq | inr bad = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inr neq1 with decidableGroups j ((j + g2) g) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inl eq1 with decidableIndex j k
  prependFrom {j} g1 g2 pr (nonempty _ (prependLetter _ g nonZero {_} (ofEmpty _ h nonZero₁) bad)) _ _ | inl refl | inr neq1 | inl eq1 | inl refl = exFalso (bad refl)
  prependFrom {_} g1 g2 pr (nonempty _ (prependLetter _ g nonZero {_} (prependLetter _ g₁ nonZero₁ x x₂) bad)) _ _ | inl refl | inr neq1 | inl eq1 | inl refl = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inl eq1 | inr j!=k with decidableIndex j j
  ... | inl refl = transitive (symmetric +Associative) (transitive (+WellDefined reflexive eq1) identRight) ,, =RP'reflex x
    where
      open Setoid (S j)
      open Group (G j)
      open Equivalence eq
  ... | inr bad = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inr neq1 | inr neq2 with decidableIndex j j
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inr neq1 | inr neq2 | inl refl with decidableGroups j ((j + g1) ((j + g2) g)) (Group.0G (G j))
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inr neq1 | inr neq2 | inl refl | inl eq1 = exFalso (neq1 (transitive (symmetric +Associative) eq1))
    where
      open Setoid (S j)
      open Group (G j)
      open Equivalence eq
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inr neq1 | inr neq2 | inl refl | inr neq3 with decidableIndex j j
  ... | inl refl = Equivalence.symmetric (Setoid.eq (S j)) (Group.+Associative (G j)) ,, =RP'reflex x
  ... | inr bad = exFalso (bad refl)
  prependFrom {.j} g1 g2 pr (nonempty _ (prependLetter j g nonZero x x₁)) _ _ | inl refl | inr neq1 | inr neq2 | inr bad = exFalso (bad refl)
  prependFrom {i} g1 g2 pr (nonempty j x) _ _  | inr i!=j with decidableIndex i i
  prependFrom {i} g1 g2 pr (nonempty j x) _ _  | inr i!=j | inl refl with decidableGroups i ((i + g1) g2) (Group.0G (G i))
  prependFrom {i} g1 g2 pr (nonempty j x) _ _ | inr i!=j | inl refl | inl eq1 = exFalso (pr eq1)
  prependFrom {i} g1 g2 pr (nonempty j x) _ _ | inr i!=j | inl refl | inr neq1 with decidableIndex i i
  prependFrom {i} g1 g2 pr (nonempty j x) _ _ | inr i!=j | inl refl | inr neq1 | inl refl = Equivalence.reflexive (Setoid.eq (S i)) ,, =RP'reflex x
  prependFrom {i} g1 g2 pr (nonempty j x) _ _ | inr i!=j | inl refl | inr neq1 | inr bad = exFalso (bad refl)
  prependFrom {i} g1 g2 pr (nonempty j x) _ _  | inr i!=j | inr bad = exFalso (bad refl)

  prependFrom' : {i : I} (g h : A i) (pr : (Setoid._∼_ (S i) (_+_ i g h) (Group.0G (G i)))) (c : ReducedSequence) .(p2 : _) .(p3 : _) → prepend i g p2 (prepend i h p3 c) =RP c
  prependFrom' {i} g h pr empty _ _ with decidableIndex i i
  prependFrom' {i} g h pr empty _ _ | inl refl with decidableGroups i ((i + g) h) (Group.0G (G i))
  ... | inl _ = record {}
  ... | inr bad = exFalso (bad pr)
  prependFrom' {i} g h pr empty _ _ | inr bad = exFalso (bad refl)
  prependFrom' {i} g h pr (nonempty j x) _ _ with decidableIndex i j
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) _ _ | inl refl with decidableGroups j ((j + h) g1) (Group.0G (G j))
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) _ _ | inl refl | inl eq1 with decidableIndex j j
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) _ _ | inl refl | inl eq1 | inl refl = transitive t (symmetric u)
    where
      open Setoid (S j)
      open Equivalence eq
      t : Setoid._∼_ (S j) g (Group.inverse (G j) h)
      t = rightInversesAreUnique (G j) pr
      u : Setoid._∼_ (S j) g1 (Group.inverse (G j) h)
      u = leftInversesAreUnique (G j) eq1
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) _ _ | inl refl | inl eq1 | inr bad = exFalso (bad refl)
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) _ _ | inl refl | inr neq with decidableIndex j j
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) p2 _ | inl refl | inr neq | inl refl with decidableGroups j ((j + g) ((j + h) g1)) (Group.0G (G j))
  ... | inl eq1 = exFalso (nonZero t)
    where
      open Setoid (S j)
      open Equivalence eq
      open Group (G j)
      t : g1 ∼ 0G
      t = transitive (transitive (symmetric identLeft) (transitive (+WellDefined (symmetric pr) reflexive) (symmetric +Associative))) eq1
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) _ _ | inl refl | inr neq | inl refl | inr neq2 with decidableIndex j j
  ... | inl refl = transitive (transitive +Associative (+WellDefined pr reflexive)) identLeft
    where
      open Setoid (S j)
      open Equivalence eq
      open Group (G j)
  ... | inr bad = exFalso (bad refl)
  prependFrom' {.j} g h pr (nonempty j (ofEmpty .j g1 nonZero)) _ _ | inl refl | inr neq | inr bad = exFalso (bad refl)
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero x x₁)) _ _ | inl refl with decidableGroups j ((j + h) g1) (Group.0G (G j))
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x bad)) _ _ | inl refl | inl eq1 with decidableIndex j k
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x bad)) _ _ | inl refl | inl eq1 | inl j=k = exFalso (bad j=k)
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x bad)) _ _ | inl refl | inl eq1 | inr j!=k with decidableIndex j j
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x bad)) _ _ | inl refl | inl eq1 | inr j!=k | inl refl = transitive {g} {inverse h} (rightInversesAreUnique (G j) pr) (symmetric (leftInversesAreUnique (G j) eq1)) ,, =RP'reflex x
    where
      open Setoid (S j)
      open Equivalence eq
      open Group (G j)
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x _)) _ _ | inl refl | inl eq1 | inr j!=k | inr bad = exFalso (bad refl)
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x x₁)) _ _ | inl refl | inr neq1 with decidableIndex j j
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inl refl with decidableGroups j ((j + g) ((j + h) g1)) (Group.0G (G j))
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inl refl | inl eq1 = exFalso (nonZero (transitive (transitive (symmetric identLeft) (transitive (+WellDefined (symmetric pr) reflexive) (symmetric +Associative))) eq1))
    where
      open Setoid (S j)
      open Equivalence eq
      open Group (G j)
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inl refl | inr neq2 with decidableIndex j j
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inl refl | inr neq2 | inl refl = transitive +Associative (transitive (+WellDefined pr reflexive) identLeft) ,, =RP'reflex x
    where
      open Setoid (S j)
      open Equivalence eq
      open Group (G j)
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inl refl | inr neq2 | inr bad = exFalso (bad refl)
  prependFrom' {.j} g h pr (nonempty j (prependLetter .j g1 nonZero {k} x x₁)) _ _ | inl refl | inr neq1 | inr bad = exFalso (bad refl)
  prependFrom' {i} g h pr (nonempty j x) _ _ | inr i!=j with decidableIndex i i
  prependFrom' {i} g h pr (nonempty j x) _ _ | inr i!=j | inl refl with decidableGroups i ((i + g) h) (Group.0G (G i))
  prependFrom' {i} g h pr (nonempty j x) _ _ | inr i!=j | inl refl | inl eq1 = =RP'reflex x
  prependFrom' {i} g h pr (nonempty j x) _ _ | inr i!=j | inl refl | inr neq1 = exFalso (neq1 pr)
  prependFrom' {i} g h pr (nonempty j x) _ _ | inr i!=j | inr bad = exFalso (bad refl)
