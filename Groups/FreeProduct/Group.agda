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

module Groups.FreeProduct.Group {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) {a b : _} {A : I → Set a} {S : (i : I) → Setoid {a} {b} (A i)} {_+_ : (i : I) → (A i) → (A i) → A i} (decidableGroups : (i : I) → (x y : A i) → ((Setoid._∼_ (S i) x y)) || ((Setoid._∼_ (S i) x y) → False)) (G : (i : I) → Group (S i) (_+_ i)) where

open import Groups.FreeProduct.Definition decidableIndex decidableGroups G
open import Groups.FreeProduct.Setoid decidableIndex decidableGroups G
open import Groups.FreeProduct.Addition decidableIndex decidableGroups G

private
  inv' : {i : I} (x : ReducedSequenceBeginningWith i) → ReducedSequence
  inv' (ofEmpty i g nonZero) = nonempty i (ofEmpty i (Group.inverse (G i) g) (λ pr → nonZero (Equivalence.transitive (Setoid.eq (S i)) (swapInv (G i) pr) (invIdent (G i)))))
  inv' (prependLetter i g nonZero {j} w i!=j) = (inv' w) +RP injection (Group.inverse (G i) g) (λ pr → nonZero (Equivalence.transitive (Setoid.eq (S i)) (swapInv (G i) pr) (invIdent (G i))))

  inv : (x : ReducedSequence) → ReducedSequence
  inv empty = empty
  inv (nonempty i w) = inv' w

private
  abstract
    lemma1 : {i j k : I} (i!=j : (i ≡ j) → False) (g : A i) (h : A j) (w : ReducedSequenceBeginningWith k) (j!=k : (j ≡ k) → False) → .(pr : _) .(pr2 : _) .(pr3 : _) → (prepend i (Group.inverse (G i) g) pr (nonempty i (prependLetter i g pr2 (prependLetter j h pr3 w j!=k) i!=j))) =RP nonempty j (prependLetter j h pr3 w j!=k)
    lemma1 {i} {j} {k} i!=j g h r j!=k pr pr2 pr3 with decidableIndex i i
    ... | inr x = exFalso (x refl)
    lemma1 {i} {j} {k} i!=j g h r j!=k pr pr2 pr3 | inl refl with decidableGroups i ((i + Group.inverse (G i) g) g) (Group.0G (G i))
    ... | inr bad = exFalso (bad (Group.invLeft (G i)))
    lemma1 {i} {j} {k} i!=j g h r j!=k pr pr2 pr3 | inl refl | inl eq1 with decidableIndex j j
    ... | inr bad = exFalso (bad refl)
    ... | inl refl = Equivalence.reflexive (Setoid.eq (S j)) ,, =RP'reflex r

  abstract
    lemma2 : {j k : I} (j!=k : (j ≡ k) → False) (h : A j) (w : ReducedSequenceBeginningWith k) .(pr : _) .(pr2 : _) → (prepend j (Group.inverse (G j) h) pr (nonempty j (prependLetter j h pr2 w j!=k))) =RP (nonempty k w)
    lemma2 {j} {k} j!=k h r pr pr2 with decidableIndex j j
    ... | inr bad = exFalso (bad refl)
    lemma2 {j} {k} j!=k h r pr pr2 | inl refl with decidableGroups j ((j + Group.inverse (G j) h) h) (Group.0G (G j))
    ... | inr bad = exFalso (bad (Group.invLeft (G j)))
    ... | inl x = =RP'reflex r

  abstract
    invRight' : {i : I} (x : ReducedSequenceBeginningWith i) → ((nonempty i x) +RP inv (nonempty i x)) =RP empty
    invRight' {i} (ofEmpty _ g nonZero) with decidableIndex i i
    ... | inr x = exFalso (x refl)
    invRight' {i} (ofEmpty _ g nonZero) | inl refl with decidableGroups i ((i + g) (Group.inverse (G i) g)) (Group.0G (G i))
    ... | inr x = exFalso (x (Group.invRight (G i)))
    ... | inl x = record {}
    invRight' {j} (prependLetter _ g nonZero {k} (ofEmpty .k h nonZero1) j!=k) with decidableIndex k j
    ... | inl x = exFalso (j!=k (equalityCommutative x))
    invRight' {j} (prependLetter _ g nonZero {k} (ofEmpty .k h nonZero1) j!=k) | inr _ with decidableIndex k k
    ... | inr x = exFalso (x refl)
    invRight' {j} (prependLetter _ g nonZero {k} (ofEmpty .k h nonZero1) j!=k) | inr _ | inl refl with decidableGroups k ((k + h) (Group.inverse (G k) h)) (Group.0G (G k))
    ... | inr x = exFalso (x (Group.invRight (G k)))
    invRight' {j} (prependLetter _ g nonZero {k} (ofEmpty .k h nonZero1) j!=k) | inr _ | inl refl | inl _ with decidableIndex j j
    ... | inr x = exFalso (x refl)
    invRight' {j} (prependLetter _ g nonZero {k} (ofEmpty .k h nonZero1) j!=k) | inr _ | inl refl | inl _ | inl refl with decidableGroups j ((j + g) (Group.inverse (G j) g)) (Group.0G (G j))
    ... | inr bad = exFalso (bad (Group.invRight (G j)))
    ... | inl r = record {}
    invRight' {j} (prependLetter _ g nonZero {k} (prependLetter .k h nonZero1 x x₁) j!=k) rewrite refl {x = 0} = {!!}

  abstract
    invRight : (x : ReducedSequence) → (x +RP (inv x)) =RP empty
    invRight empty = record {}
    invRight (nonempty i w) = invRight' {i} w

  abstract
    invLeft' : {i : I} (x : ReducedSequenceBeginningWith i) → (inv (nonempty i x) +RP (nonempty i x)) =RP empty
    invLeft' {i} (ofEmpty .i g nonZero) with decidableIndex i i
    invLeft' {i} (ofEmpty .i g nonZero) | inl refl with decidableGroups i ((i + Group.inverse (G i) g) g) (Group.0G (G i))
    ... | inl good = record {}
    ... | inr bad = exFalso (bad (Group.invLeft (G i) {g}))
    invLeft' {i} (ofEmpty .i g nonZero) | inr x = exFalso (x refl)
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j g₁ nonZero₁) i!=j) with decidableIndex j i
    ... | inl pr = exFalso (i!=j (equalityCommutative pr))
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j g₁ nonZero₁) i!=j) | inr pr with decidableIndex i i
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j g₁ nonZero₁) i!=j) | inr pr | inl refl with decidableGroups i ((i + Group.inverse (G i) g) g) (Group.0G (G i))
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j g₁ nonZero₁) i!=j) | inr pr | inl refl | inl k with decidableIndex j j
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j h nonZero₁) i!=j) | inr pr | inl refl | inl k | inl refl with decidableGroups j ((j + Group.inverse (G j) h) h) (Group.0G (G j))
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j h nonZero₁) i!=j) | inr pr | inl refl | inl k | inl refl | inl good = record {}
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j h nonZero₁) i!=j) | inr pr | inl refl | inl k | inl refl | inr bad = exFalso (bad (Group.invLeft (G j)))
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j g₁ nonZero₁) i!=j) | inr pr | inl refl | inl k | inr bad = exFalso (bad refl)
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j g₁ nonZero₁) i!=j) | inr pr | inl refl | inr k = exFalso (k (Group.invLeft (G i) {g}))
    invLeft' {i} (prependLetter .i g nonZero {.j} (ofEmpty j g₁ nonZero₁) i!=j) | inr pr | inr bad = exFalso (bad refl)
    invLeft' {i} (prependLetter .i g nonZero {.j} (prependLetter j h nonZero1 {k} w x) i!=j) = Equivalence.transitive (Setoid.eq freeProductSetoid) {(((inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)) +RP nonempty i (ofEmpty i (Group.inverse (G i) g) _)) +RP nonempty i (prependLetter i g _ (prependLetter j h _ w x) i!=j))} {_} {empty} (plusAssoc (inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)) (nonempty i (ofEmpty i (Group.inverse (G i) g) _)) (nonempty i (prependLetter i g _ (prependLetter j h _ w x) i!=j))) (Equivalence.transitive (Setoid.eq freeProductSetoid) {((inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)) +RP (prepend i (Group.inverse (G i) g) _ (nonempty i (prependLetter i g _ (prependLetter j h _ w x) i!=j))))} {(inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)) +RP (nonempty j (prependLetter j h nonZero1 w x))} {empty} (plusWD (inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)) (prepend i (Group.inverse (G i) g) _ (nonempty i (prependLetter i g _ (prependLetter j h _ w x) i!=j))) (inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)) (nonempty j (prependLetter j h _ w x)) (Equivalence.reflexive (Setoid.eq freeProductSetoid) {inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)}) (lemma1 {i} {j} {k} i!=j g h w x (λ p → nonZero (invZeroImpliesZero (G i) p)) nonZero nonZero1)) (Equivalence.transitive (Setoid.eq freeProductSetoid) {(inv' w +RP nonempty j (ofEmpty j (Group.inverse (G j) h) _)) +RP nonempty j (prependLetter j h _ w x)} {inv' w +RP (nonempty j (ofEmpty j (Group.inverse (G j) h) λ p → nonZero1 (invZeroImpliesZero (G j) p)) +RP nonempty j (prependLetter j h nonZero1 w x))} {empty} (plusAssoc (inv' w) (nonempty j (ofEmpty j (Group.inverse (G j) h) _)) (nonempty j (prependLetter j h _ w x))) (Equivalence.transitive (Setoid.eq freeProductSetoid) {inv' w +RP (prepend j (Group.inverse (G j) h) _ (nonempty j (prependLetter j h nonZero1 w x)))} {inv' w +RP (nonempty k w)} {empty} (plusWD (inv' w) (prepend j (Group.inverse (G j) h) _ (nonempty j (prependLetter j h nonZero1 w x))) (inv' w) (nonempty k w) (Equivalence.reflexive (Setoid.eq freeProductSetoid) {inv' w}) (lemma2 {j} {k} x h w (λ p → nonZero1 (invZeroImpliesZero (G j) p)) nonZero1)) (invLeft' {k} w))))

  abstract
    invLeft : (x : ReducedSequence) → ((inv x) +RP x) =RP empty
    invLeft empty = record {}
    invLeft (nonempty i w) = invLeft' {i} w

FreeProductGroup : Group freeProductSetoid _+RP_
Group.+WellDefined FreeProductGroup {m} {n} {x} {y} m=x n=y = plusWD m n x y m=x n=y
Group.0G FreeProductGroup = empty
Group.inverse FreeProductGroup = inv
Group.+Associative FreeProductGroup {a} {b} {c} = Equivalence.symmetric (Setoid.eq freeProductSetoid) {(a +RP b) +RP c} {a +RP (b +RP c)} (plusAssoc a b c)
Group.identRight FreeProductGroup {empty} = Equivalence.reflexive (Setoid.eq freeProductSetoid) {empty}
Group.identRight FreeProductGroup {nonempty i x} rewrite refl {x = 0} = plusEmptyRight x
Group.identLeft FreeProductGroup {empty} = Equivalence.reflexive (Setoid.eq freeProductSetoid) {empty}
Group.identLeft FreeProductGroup {nonempty i x} = Equivalence.reflexive (Setoid.eq freeProductSetoid) {nonempty i x}
Group.invLeft FreeProductGroup {x} = invLeft x
Group.invRight FreeProductGroup {x} = invRight x
