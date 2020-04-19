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

module Groups.FreeProduct.Setoid {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) {a b : _} {A : I → Set a} {S : (i : I) → Setoid {a} {b} (A i)} {_+_ : (i : I) → (A i) → (A i) → A i} (decidableGroups : (i : I) → (x y : A i) → ((Setoid._∼_ (S i) x y)) || ((Setoid._∼_ (S i) x y) → False)) (G : (i : I) → Group (S i) (_+_ i)) where

open import Groups.FreeProduct.Definition decidableIndex decidableGroups G

=RP' : {m n : _} (s1 : ReducedSequenceBeginningWith m) (s2 : ReducedSequenceBeginningWith n) → Set b
=RP' (ofEmpty i g nonZero) (ofEmpty j h nonZero₁) with decidableIndex i j
=RP' (ofEmpty i g nonZero) (ofEmpty .i h nonZero₁) | inl refl = Setoid._∼_ (S i) g h
=RP' (ofEmpty i g nonZero) (ofEmpty j h nonZero₁) | inr x = False'
=RP' (ofEmpty i g nonZero) (prependLetter i₁ g₁ nonZero₁ s2 x) = False'
=RP' (prependLetter i g nonZero s1 x) (ofEmpty i₁ g₁ nonZero₁) = False'
=RP' (prependLetter i g nonZero s1 x) (prependLetter j h nonZero₁ s2 x₁) with decidableIndex i j
=RP' (prependLetter i g nonZero s1 x) (prependLetter .i h nonZero₁ s2 x₁) | inl refl = Setoid._∼_ (S i) g h && =RP' s1 s2
=RP' (prependLetter i g nonZero s1 x) (prependLetter j h nonZero₁ s2 x₁) | inr x₂ = False'

_=RP_ : Rel ReducedSequence
empty =RP empty = True'
empty =RP nonempty i x = False'
nonempty i x =RP empty = False'
nonempty i x =RP nonempty j y = =RP' x y

=RP'reflex : {i : _} (x : ReducedSequenceBeginningWith i) → =RP' x x
=RP'reflex (ofEmpty i g nonZero) with decidableIndex i i
=RP'reflex (ofEmpty i g nonZero) | inl refl = Equivalence.reflexive (Setoid.eq (S i))
=RP'reflex (ofEmpty i g nonZero) | inr x = exFalso (x refl)
=RP'reflex (prependLetter i g nonZero x x₁) with decidableIndex i i
=RP'reflex (prependLetter i g nonZero x x₁) | inl refl = Equivalence.reflexive (Setoid.eq (S i)) ,, =RP'reflex x
=RP'reflex (prependLetter i g nonZero x x₁) | inr bad = exFalso (bad refl)

private
  reflex : Reflexive _=RP_
  reflex {empty} = record {}
  reflex {nonempty i (ofEmpty .i g nonZero)} with decidableIndex i i
  reflex {nonempty i (ofEmpty .i g nonZero)} | inl refl = Equivalence.reflexive (Setoid.eq (S i))
  ... | inr bad = exFalso (bad refl)
  reflex {nonempty i (prependLetter .i g nonZero x x₁)} with decidableIndex i i
  reflex {nonempty i (prependLetter .i g nonZero x x₁)} | inl refl = Equivalence.reflexive (Setoid.eq (S i)) ,, =RP'reflex x
  reflex {nonempty i (prependLetter .i g nonZero x x₁)} | inr bad = exFalso (bad refl)

=RP'symm : {i j : _} (x : ReducedSequenceBeginningWith i) (y : ReducedSequenceBeginningWith j) → =RP' x y → =RP' y x
=RP'symm (ofEmpty i g nonZero) (ofEmpty j h nonZero2) with decidableIndex i j
=RP'symm (ofEmpty i g nonZero) (ofEmpty j h nonZero2) | inl pr with decidableIndex j i
=RP'symm (ofEmpty .j g nonZero) (ofEmpty j h nonZero2) | inl refl | inl refl = Equivalence.symmetric (Setoid.eq (S j)) {g} {h}
=RP'symm (ofEmpty i g nonZero) (ofEmpty j h nonZero2) | inl pr | inr x = exFalso (x (equalityCommutative pr))
=RP'symm (ofEmpty i g nonZero) (ofEmpty j h nonZero2) | inr x with decidableIndex j i
=RP'symm (ofEmpty i g nonZero) (ofEmpty j h nonZero2) | inr x | inl pr = exFalso (x (equalityCommutative pr))
=RP'symm (ofEmpty i g nonZero) (ofEmpty j h nonZero2) | inr x | inr _ = id
=RP'symm (ofEmpty i g nonZero) (prependLetter i₁ g₁ nonZero₁ y x) = id
=RP'symm (prependLetter i g nonZero x x₁) (ofEmpty i₁ g₁ nonZero₁) = id
=RP'symm (prependLetter i g nonZero x x₁) (prependLetter j h nonZero2 y pr2) pr with decidableIndex i j
=RP'symm (prependLetter .j g nonZero x x₁) (prependLetter j h nonZero2 y pr2) pr | inl refl with decidableIndex j j
=RP'symm (prependLetter .j g nonZero x x₁) (prependLetter j h nonZero2 y pr2) (fst ,, snd) | inl refl | inl refl = Equivalence.symmetric (Setoid.eq (S j)) fst ,, =RP'symm x y snd
=RP'symm (prependLetter .j g nonZero x x₁) (prependLetter j h nonZero2 y pr2) pr | inl refl | inr bad = exFalso (bad refl)
=RP'symm (prependLetter i g nonZero x x₁) (prependLetter j h nonZero2 y pr2) () | inr i!=j

private
  symm : Symmetric _=RP_
  symm {empty} {empty} x = record {}
  symm {nonempty i m} {nonempty i₁ n} x = =RP'symm m n x

=RP'trans : {i j k : _} (x : ReducedSequenceBeginningWith i) (y : ReducedSequenceBeginningWith j) (z : ReducedSequenceBeginningWith k) → =RP' x y → =RP' y z → =RP' x z
=RP'trans (ofEmpty i g nonZero) (ofEmpty j g₁ nonZero₁) (ofEmpty k g₂ nonZero₂) x=y y=z with decidableIndex i j
=RP'trans (ofEmpty .j g nonZero) (ofEmpty j g₁ nonZero₁) (ofEmpty k g₂ nonZero₂) x=y y=z | inl refl with decidableIndex j k
=RP'trans (ofEmpty .j g nonZero) (ofEmpty j g₁ nonZero₁) (ofEmpty .j g₂ nonZero₂) x=y y=z | inl refl | inl refl = Equivalence.transitive (Setoid.eq (S j)) x=y y=z
=RP'trans (prependLetter i g nonZero x x₁) (prependLetter j g₁ nonZero₁ y x₂) (prependLetter k g₂ nonZero₂ z x₃) x=y y=z with decidableIndex i j
=RP'trans (prependLetter .j g nonZero x x₁) (prependLetter j g₁ nonZero₁ y x₂) (prependLetter k g₂ nonZero₂ z x₃) x=y y=z | inl refl with decidableIndex j k
=RP'trans (prependLetter .j g nonZero x x₁) (prependLetter j g₁ nonZero₁ y x₂) (prependLetter .j g₂ nonZero₂ z x₃) (fst1 ,, snd1) (fst2 ,, snd2) | inl refl | inl refl = Equivalence.transitive (Setoid.eq (S j)) fst1 fst2 ,, =RP'trans x y z snd1 snd2

private
  trans : (x y z : ReducedSequence) → x =RP y → y =RP z → x =RP z
  trans empty empty empty x=y y=z = record {}
  trans (nonempty i x) (nonempty i₁ y) (nonempty i₂ z) x=y y=z = =RP'trans x y z x=y y=z

notEqualIfStartDifferent : {j1 j2 : I} (neq : (j1 ≡ j2) → False) → (x1 : ReducedSequenceBeginningWith j1) (x2 : ReducedSequenceBeginningWith j2) → =RP' x1 x2 → False
notEqualIfStartDifferent neq (ofEmpty i g nonZero) (ofEmpty j g₁ nonZero₁) eq with decidableIndex i j
notEqualIfStartDifferent neq (ofEmpty i g nonZero) (ofEmpty j g₁ nonZero₁) eq | inl i=j = neq i=j
notEqualIfStartDifferent neq (prependLetter i g nonZero x1 x) (prependLetter j g₁ nonZero₁ x2 x₁) eq with decidableIndex i j
notEqualIfStartDifferent neq (prependLetter i g nonZero x1 x) (prependLetter j g₁ nonZero₁ x2 x₁) eq | inl eq' = neq eq'

freeProductSetoid : Setoid ReducedSequence
Setoid._∼_ freeProductSetoid = _=RP_
Equivalence.reflexive (Setoid.eq freeProductSetoid) {x} = reflex {x}
Equivalence.symmetric (Setoid.eq freeProductSetoid) {a} {b} = symm {a} {b}
Equivalence.transitive (Setoid.eq freeProductSetoid) {x} {y} {z} = trans x y z

