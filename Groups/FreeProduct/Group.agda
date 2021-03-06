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

module Groups.FreeProduct.Group {i : _} {I : Set i} (decidableIndex : (x y : I) → ((x ≡ y) || ((x ≡ y) → False))) {a b : _} {A : I → Set a} {S : (i : I) → Setoid {a} {b} (A i)} {_+_ : (i : I) → (A i) → (A i) → A i} (decidableGroups : (i : I) → (x y : A i) → ((Setoid._∼_ (S i) x y)) || ((Setoid._∼_ (S i) x y) → False)) (G : (i : I) → Group (S i) (_+_ i)) where

open import Groups.FreeProduct.Definition decidableIndex decidableGroups G
open import Groups.FreeProduct.Setoid decidableIndex decidableGroups G
open import Groups.FreeProduct.Addition decidableIndex decidableGroups G

private
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
  plusWD : (m n o p : ReducedSequence) → (m =RP o) → (n =RP p) → (m +RP n) =RP (o +RP p)
  plusWD empty empty empty empty m=o n=p = record {}
  plusWD empty (nonempty i x) empty (nonempty i₁ x₁) m=o n=p = n=p
  plusWD (nonempty i x) empty (nonempty j y) empty m=o record {} = Equivalence.transitive (Setoid.eq freeProductSetoid) {plus' x empty} {nonempty i x} {plus' y empty} (plusEmptyRight x) (Equivalence.transitive (Setoid.eq freeProductSetoid) {nonempty i x} {nonempty j y} {plus' y empty} m=o (Equivalence.symmetric (Setoid.eq freeProductSetoid) {plus' y empty} {nonempty j y} (plusEmptyRight y)))
  plusWD (nonempty i1 x1) (nonempty i2 x2) (nonempty i3 x3) (nonempty i4 x4) m=o n=p = (Equivalence.transitive (Setoid.eq freeProductSetoid)) {plus' x1 (nonempty i2 x2)} {plus' x3 (nonempty i2 x2)} {plus' x3 (nonempty i4 x4)} (plus'WD x1 x3 (nonempty i2 x2) m=o) (plus'WD' x3 (nonempty i2 x2) (nonempty i4 x4) n=p)

  prependAssocLemma' : {i : I} {g : A i} .(nz : Setoid._∼_ (S i) g (Group.0G (G i)) → False) (b c : ReducedSequence) → (prepend i g nz b +RP c) =RP prepend i g nz (b +RP c)
  prependAssocLemma' {i} {g} nz empty c = Equivalence.reflexive (Setoid.eq freeProductSetoid) {prepend i g _ c}
  prependAssocLemma' {i} nz (nonempty k x) c with decidableIndex i k
  prependAssocLemma' {.k} {g1} nz (nonempty k (ofEmpty .k g nonZero)) c | inl refl with decidableGroups k ((k + g1) g) (Group.0G (G k))
  prependAssocLemma' {.k} {g1} nz (nonempty k (ofEmpty .k g nonZero)) c | inl refl | inl eq1 = Equivalence.symmetric (Setoid.eq freeProductSetoid) {prepend k g1 _ (prepend k g _ c)} {c} (prependFrom' g1 g eq1 c nz nonZero)
  prependAssocLemma' {.k} {g1} nz (nonempty k (ofEmpty .k g nonZero)) c | inl refl | inr neq1 = (prependFrom g1 g neq1 c nz nonZero)
  prependAssocLemma' {.k} {g1} nz (nonempty k (prependLetter .k g nonZero x x₁)) c | inl refl with decidableGroups k ((k + g1) g) (Group.0G (G k))
  prependAssocLemma' {.k} {g1} nz (nonempty k (prependLetter .k g nonZero x x₁)) c | inl refl | inl eq1 = Equivalence.symmetric (Setoid.eq freeProductSetoid) {prepend k g1 _ (prepend k g _ (plus' x c))} {plus' x c} (prependFrom' g1 g eq1 (plus' x c) nz nonZero)
  prependAssocLemma' {.k} {g1} nz (nonempty k (prependLetter .k g nonZero x x₁)) c | inl refl | inr neq1 = prependFrom g1 g neq1 (plus' x c) nz nonZero
  prependAssocLemma' {i} {g} nz (nonempty k x) c | inr i!=k = Equivalence.reflexive (Setoid.eq freeProductSetoid) {prepend i g _ (plus' x c)}

  plusAssocLemma : {i : I} (x : ReducedSequenceBeginningWith i) (b c : ReducedSequence) → (plus' x b +RP c) =RP plus' x (b +RP c)
  plusAssocLemma (ofEmpty i g nonZero) empty c = Equivalence.reflexive (Setoid.eq freeProductSetoid) {prepend i g _ c}
  plusAssocLemma (ofEmpty i g nonZero) (nonempty j b) c with decidableIndex i j
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (ofEmpty .i g₁ nonZero₁)) c | inl refl with decidableIndex i i
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (ofEmpty .i h nonZero₁)) c | inl refl | inl refl with decidableGroups i ((i + g) h) (Group.0G (G i))
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (ofEmpty .i h nonZero₁)) c | inl refl | inl refl | inl t = Equivalence.symmetric (Setoid.eq freeProductSetoid) {prepend i g _ (prepend i h _ c)} {c} (prependFrom' g h t c _ _)
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (ofEmpty .i h nonZero₁)) c | inl refl | inl refl | inr t = prependFrom g h t c _ _
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (ofEmpty .i g₁ nonZero₁)) c | inl refl | inr bad = exFalso (bad refl)
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (prependLetter .i h nonZero₁ b x)) c | inl refl with decidableGroups i ((i + g) h) (Group.0G (G i))
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (prependLetter .i h nonZero₁ b x)) c | inl refl | inl eq1 = Equivalence.symmetric (Setoid.eq freeProductSetoid) {prepend i g _ (prepend i h _ (plus' b c))} {plus' b c} (prependFrom' g h eq1 (plus' b c) _ _)
  plusAssocLemma (ofEmpty i g nonZero) (nonempty .i (prependLetter .i h nonZero₁ b x)) c | inl refl | inr neq1 = prependFrom g h neq1 (plus' b c) nonZero _
  plusAssocLemma (ofEmpty i g nonZero) (nonempty j b) c | inr i!=j = Equivalence.reflexive (Setoid.eq freeProductSetoid) {prepend i g _ (plus' b c)}
  plusAssocLemma (prependLetter i g nonZero {j} w i!=j) b c = Equivalence.transitive (Setoid.eq freeProductSetoid) {prepend i g _ (plus' w b) +RP c} {prepend i g _ (plus' w b +RP c)} {prepend i g _ (plus' w (b +RP c))} (prependAssocLemma' nonZero (plus' w b) c) (prependWD' g nonZero (plus' w b +RP c) (plus' w (b +RP c)) (plusAssocLemma w b c))

  plusAssoc : (a b c : ReducedSequence) → ((a +RP b) +RP c) =RP (a +RP (b +RP c))
  plusAssoc empty b c = Equivalence.reflexive (Setoid.eq freeProductSetoid) {b +RP c}
  plusAssoc (nonempty i x) b c = plusAssocLemma x b c


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
    unpeel : (k : ReducedSequence) {j : I} (g : A j) .(pr : _) .(pr2 : _) → k =RP empty → (prepend j g pr (k +RP (nonempty j (ofEmpty j (Group.inverse (G j) g) pr2)))) =RP empty
    unpeel empty {j} g pr pr2 x with decidableIndex j j
    ... | inr bad = exFalso (bad refl)
    unpeel empty {j} g pr pr2 x | inl refl with decidableGroups j ((j + g) (Group.inverse (G j) g)) (Group.0G (G j))
    ... | inl _ = record {}
    ... | inr bad = exFalso (bad (Group.invRight (G j)))

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
    invRight' {j} (prependLetter _ g nonZero {k} (prependLetter .k h nonZero1 {i} x k!=i) j!=k) rewrite refl {x = 0} = Equivalence.transitive (Setoid.eq freeProductSetoid) {prepend j g _ (prepend k h _ (plus' x ((inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) _)) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) _))))} {prepend j g nonZero (prepend k h nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G k) t)))) +RP (nonempty j (ofEmpty j (Group.inverse (G j) g) λ t → nonZero (invZeroImpliesZero (G j) t))))} {empty} (prependWD' g nonZero (prepend k h nonZero1 (plus' x ((inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) _)) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) λ t → nonZero (invZeroImpliesZero (G j) t))))) (prepend k h _ (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G k) t)))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) λ i → nonZero (invZeroImpliesZero (G j) i))) (Equivalence.symmetric (Setoid.eq freeProductSetoid) {(prepend k h _ (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) _))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) _))} {prepend k h _ (plus' x ((inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) _)) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) _)))} t)) (unpeel (prepend k h nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) _)))) g nonZero (λ t → nonZero (invZeroImpliesZero (G j) t)) (Equivalence.transitive (Setoid.eq freeProductSetoid) {prepend k h nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G k) t))))} {prepend k h nonZero1 ((plus' x (inv' x)) +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G k) t)))} {empty} (prependWD' h nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G k) t)))) (plus' x (inv' x) +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G k) t))) (Equivalence.symmetric (Setoid.eq freeProductSetoid) {plus' x (inv' x) +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G k) t))} (plusAssoc (nonempty _ x) (inv' x) (nonempty k (ofEmpty k (Group.inverse (G k) h) (λ t → nonZero1 (invZeroImpliesZero (G k) t))))))) (unpeel (plus' x (inv' x)) h nonZero1 (λ t → nonZero1 (invZeroImpliesZero (G k) t)) (invRight' x))))
      where
        t : (prepend k h nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) (λ t → nonZero1 (invZeroImpliesZero (G _) t))))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) (λ t → nonZero (invZeroImpliesZero (G j) t)))) =RP (prepend k h nonZero1 (plus' x ((inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) (λ t → nonZero1 (invZeroImpliesZero (G _) t)))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) (λ t → nonZero (invZeroImpliesZero (G j) t))))))
        t = Equivalence.transitive (Setoid.eq freeProductSetoid) {(prepend k h nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) (λ t → nonZero1 (invZeroImpliesZero (G _) t))))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) (λ t → nonZero (invZeroImpliesZero (G j) t))))} {prepend k h _ (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G _) t))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) λ t → nonZero (invZeroImpliesZero (G _) t)))} {(prepend k h nonZero1 (plus' x ((inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) (λ t → nonZero1 (invZeroImpliesZero (G _) t)))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) (λ t → nonZero (invZeroImpliesZero (G j) t))))))} (prependAssocLemma' {k} {h} nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) _))) (nonempty j (ofEmpty j (Group.inverse (G j) g) _))) (prependWD' h nonZero1 (plus' x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G _) t))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) λ t → nonZero (invZeroImpliesZero (G _) t))) (plus' x ((inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G _) t))) +RP nonempty j (ofEmpty j (Group.inverse (G j) g) λ t → nonZero (invZeroImpliesZero (G _) t)))) (plusAssocLemma x (inv' x +RP nonempty k (ofEmpty k (Group.inverse (G k) h) λ t → nonZero1 (invZeroImpliesZero (G _) t))) (nonempty j (ofEmpty j (Group.inverse (G j) g) λ t → nonZero (invZeroImpliesZero (G _) t)))))

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
