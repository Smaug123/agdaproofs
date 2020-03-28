{-# OPTIONS --safe --warning=error #-}

open import Sets.EquivalenceRelations
open import Functions
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

prepend : (i : I) → (g : A i) → (nonZero : (Setoid._∼_ (S i) g (Group.0G (G i))) → False) → ReducedSequence → ReducedSequence
prepend i g nonzero empty = nonempty i (ofEmpty i g nonzero)
prepend i g nonzero (nonempty j x) with decidableIndex i j
prepend i g nonzero (nonempty .i (ofEmpty .i h nonZero)) | inl refl with decidableGroups i (_+_ i g h) (Group.0G (G i))
prepend i g nonzero (nonempty .i (ofEmpty .i h nonZero)) | inl refl | inl sumZero = empty
prepend i g nonzero (nonempty .i (ofEmpty .i h nonZero)) | inl refl | inr sumNotZero = nonempty i (ofEmpty i (_+_ i g h) sumNotZero)
prepend i g nonzero (nonempty .i (prependLetter .i h nonZero x x₁)) | inl refl with decidableGroups i (_+_ i g h) (Group.0G (G i))
prepend i g nonzero (nonempty .i (prependLetter .i h nonZero {j} x x₁)) | inl refl | inl sumZero = nonempty j x
prepend i g nonzero (nonempty .i (prependLetter .i h nonZero x pr)) | inl refl | inr sumNotZero = nonempty i (prependLetter i (_+_ i g h) sumNotZero x pr)
prepend i g nonzero (nonempty j x) | inr i!=j = nonempty i (prependLetter i g nonzero x i!=j)

plus' : {j : _} → (ReducedSequenceBeginningWith j) → ReducedSequence → ReducedSequence
plus' (ofEmpty i g nonZero) s = prepend i g nonZero s
plus' (prependLetter i g nonZero x pr) s = prepend i g nonZero (plus' x s)

_+RP_ : ReducedSequence → ReducedSequence → ReducedSequence
empty +RP b = b
nonempty i x +RP b = plus' x b

abstract
  prependWD : {i : I} → (g1 g2 : A i) → (nz1 : _) → (nz2 : _) → (y : ReducedSequence) (eq : Setoid._∼_ (S i) g1 g2) → prepend i g1 nz1 y =RP prepend i g2 nz2 y
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
  prependWD' : {i : I} → (g : A i) → (nz : _) → (y1 y2 : ReducedSequence) (eq : y1 =RP y2) → prepend i g nz y1 =RP prepend i g nz y2
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

plus'WDlemm : {i : I} (x1 x2 : ReducedSequenceBeginningWith i) (y : ReducedSequence) → (=RP' x1 x2) → plus' x1 y =RP plus' x2 y
plus'WDlemm (ofEmpty i g nonZero) (ofEmpty .i g₁ nonZero₁) y x1=x2 with decidableIndex i i
plus'WDlemm (ofEmpty i g nonZero) (ofEmpty .i h nonZero2) y x1=x2 | inl refl = prependWD g h nonZero nonZero2 y x1=x2
plus'WDlemm (prependLetter i g nonZero {j} x1 x) (prependLetter .i h nonZero2 {j2} x2 pr) y x1=x2 with decidableIndex i i
... | inl refl with decidableIndex j j2
plus'WDlemm (prependLetter i g nonZero {j} x1 x) (prependLetter .i h nonZero2 {.j} x2 pr) y x1=x2 | inl refl | inl refl = Equivalence.transitive (Setoid.eq freeProductSetoid) {prepend i g nonZero (plus' x1 y)} {prepend i h nonZero2 (plus' x1 y)} {plus' (prependLetter i h nonZero2 x2 pr) y} (prependWD g h nonZero nonZero2 (plus' x1 y) (_&&_.fst x1=x2)) (prependWD' h nonZero2 (plus' x1 y) (plus' x2 y) (plus'WDlemm x1 x2 y (_&&_.snd x1=x2)))
... | inr j!=j2 = exFalso (notEqualIfStartDifferent j!=j2 x1 x2 (_&&_.snd x1=x2))
plus'WDlemm _ _ _ _ | inr bad = exFalso (bad refl)

plus'WD : {i j : I} (x1 : ReducedSequenceBeginningWith i) (x2 : ReducedSequenceBeginningWith j) (y : ReducedSequence) → (=RP' x1 x2) → plus' x1 y =RP plus' x2 y
plus'WD {i} {j} x1 x2 y x1=x2 with decidableIndex i j
plus'WD {i} {.i} x1 x2 y x1=x2 | inl refl = plus'WDlemm x1 x2 y x1=x2
plus'WD {i} {j} x1 x2 y x1=x2 | inr x = exFalso (notEqualIfStartDifferent x x1 x2 x1=x2)

private
  prependLetterWD : {i : I} {h1 h2 : A i} (h1=h2 : Setoid._∼_ (S i) h1 h2) → (nonZero1 : _) (nonZero2 : _) {j1 j2 : I} (w1 : ReducedSequenceBeginningWith j1) (w2 : ReducedSequenceBeginningWith j2) → (eq : =RP' w1 w2) → (x1 : i ≡ _ → False) (x2 : i ≡ _ → False) → nonempty i (prependLetter i h1 nonZero1 w1 x1) =RP nonempty i (prependLetter i h2 nonZero2 w2 x2)
  prependLetterWD {i} h1=h2 nonZero1 nonZero2 {j1} {j2} w1 w2 eq x1 x2 with decidableIndex i i
  prependLetterWD {i} h1=h2 nonZero1 nonZero2 {j1} {j2} w1 w2 eq x1 x2 | inl refl = h1=h2 ,, eq
  prependLetterWD {i} h1=h2 nonZero1 nonZero2 {j1} {j2} w1 w2 eq x1 x2 | inr x = exFalso (x refl)

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

private
  plusEmpty : {i : I} (x : ReducedSequenceBeginningWith i) → _=RP_ (plus' x empty) (nonempty i x)
  plusEmpty (ofEmpty i g nonZero) with decidableIndex i i
  plusEmpty (ofEmpty i g nonZero) | inl refl = Equivalence.reflexive (Setoid.eq (S i))
  plusEmpty (ofEmpty i g nonZero) | inr x = exFalso (x refl)
  plusEmpty (prependLetter i g nonZero {j} x i!=j) with plusEmpty x
  ... | b with plus' x empty
  plusEmpty (prependLetter i g nonZero {j} x i!=j) | b | nonempty k w with decidableIndex i k
  plusEmpty (prependLetter .k g nonZero {j} x i!=j) | b | nonempty k (ofEmpty .k h nonZero₁) | inl refl with decidableGroups k ((k + g) h) (Group.0G (G k))
  plusEmpty (prependLetter .k g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty k (ofEmpty .k h nonZero₁) | inl refl | inl g+k=hinv with decidableIndex k i
  plusEmpty (prependLetter .i g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty .i (ofEmpty .i h nonZero₁) | inl refl | inl g+k=hinv | inl refl = exFalso (i!=j refl)
  plusEmpty (prependLetter .k g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty k (ofEmpty .k h nonZero₁) | inl refl | inr x₁ with decidableIndex k i
  plusEmpty (prependLetter .i g nonZero {.i} (ofEmpty i g₁ nonZero₂) i!=j) | b | nonempty .i (ofEmpty .i h nonZero₁) | inl refl | inr x₁ | inl refl = exFalso (i!=j refl)
  plusEmpty (prependLetter .k g nonZero {j} w1 i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl with decidableGroups k ((k + g) h) (Group.0G (G k))
  plusEmpty (prependLetter .k g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inl p with decidableIndex k i
  plusEmpty (prependLetter .i g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty .i (prependLetter .i h nonZero₁ w x₁) | inl refl | inl p | inl refl = exFalso (i!=j refl)
  plusEmpty (prependLetter .k g nonZero {j} w1 i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inr x₂ with decidableIndex k k
  plusEmpty (prependLetter .k g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inr x₂ | inl refl with decidableIndex k i
  plusEmpty (prependLetter .i g nonZero {.i} (prependLetter i g₁ nonZero₂ w1 x) i!=j) | b | nonempty .i (prependLetter .i h nonZero₁ w x₁) | inl refl | inr x₂ | inl refl | inl refl = exFalso (i!=j refl)
  plusEmpty (prependLetter .k g nonZero {j} w1 i!=j) | b | nonempty k (prependLetter .k h nonZero₁ w x₁) | inl refl | inr x₂ | inr x = exFalso (x refl)
  plusEmpty (prependLetter i g nonZero {j} w1 i!=j) | b | nonempty k w | inr i!=k with decidableIndex i i
  plusEmpty (prependLetter i g nonZero {j} w1 i!=j) | b | nonempty k w | inr i!=k | inl refl = Equivalence.reflexive (Setoid.eq (S i)) ,, b
  plusEmpty (prependLetter i g nonZero {j} w1 i!=j) | b | nonempty k w | inr i!=k | inr x = exFalso (x refl)

plusWD : (m n o p : ReducedSequence) → (m =RP o) → (n =RP p) → (m +RP n) =RP (o +RP p)
plusWD empty empty empty empty m=o n=p = record {}
plusWD empty (nonempty i x) empty (nonempty i₁ x₁) m=o n=p = n=p
plusWD (nonempty i x) empty (nonempty j y) empty m=o record {} = Equivalence.transitive (Setoid.eq freeProductSetoid) {plus' x empty} {nonempty i x} {plus' y empty} (plusEmpty x) (Equivalence.transitive (Setoid.eq freeProductSetoid) {nonempty i x} {nonempty j y} {plus' y empty} m=o (Equivalence.symmetric (Setoid.eq freeProductSetoid) {plus' y empty} {nonempty j y} (plusEmpty y)))
plusWD (nonempty i1 x1) (nonempty i2 x2) (nonempty i3 x3) (nonempty i4 x4) m=o n=p = (Equivalence.transitive (Setoid.eq freeProductSetoid)) {plus' x1 (nonempty i2 x2)} {plus' x3 (nonempty i2 x2)} {plus' x3 (nonempty i4 x4)} (plus'WD x1 x3 (nonempty i2 x2) m=o) (plus'WD' x3 (nonempty i2 x2) (nonempty i4 x4) n=p)
