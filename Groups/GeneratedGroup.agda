{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Setoids.Setoids
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Sets.FinSet
open import Groups.GroupDefinition
open import Vectors
open import Orders
open import Groups.Groups

module Groups.GeneratedGroup where
  data FreeCompletion {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
    ofLetter : A → FreeCompletion S
    ofInv : A → FreeCompletion S

  freeCompletionMap : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) → FreeCompletion S → FreeCompletion T
  freeCompletionMap f (ofLetter x) = ofLetter (f x)
  freeCompletionMap f (ofInv x) = ofInv (f x)

  freeInverse : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (l : FreeCompletion S) → FreeCompletion S
  freeInverse (ofLetter x) = ofInv x
  freeInverse (ofInv x) = ofLetter x

  freeCompletionSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (FreeCompletion S)
  (freeCompletionSetoid S Setoid.∼ ofLetter w) (ofLetter x) = Setoid._∼_ S w x
  (freeCompletionSetoid S Setoid.∼ ofLetter w) (ofInv x) = False'
  (freeCompletionSetoid S Setoid.∼ ofInv w) (ofLetter x) = False'
  (freeCompletionSetoid S Setoid.∼ ofInv w) (ofInv x) = Setoid._∼_ S w x
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter x} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv x} = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofLetter x} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofInv x} ()
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofLetter x} ()
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofInv x} = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofLetter x} {ofLetter y} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofLetter x} {ofInv y} _ ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofLetter w} {ofInv x} {y} ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofLetter x} {y} ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofInv x} {ofLetter y} _ ()
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (freeCompletionSetoid S))) {ofInv w} {ofInv x} {ofInv y} = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))

  freeCompletionMapWellDefined : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) → ({x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)) → {x y : FreeCompletion S} → (Setoid._∼_ (freeCompletionSetoid S) x y) → (Setoid._∼_ (freeCompletionSetoid T) (freeCompletionMap f x) (freeCompletionMap f y))
  freeCompletionMapWellDefined f fWD {ofLetter x} {ofLetter x₁} w1=w2 = fWD w1=w2
  freeCompletionMapWellDefined f fWD {ofLetter x} {ofInv x₁} ()
  freeCompletionMapWellDefined f fWD {ofInv x} {ofLetter x₁} ()
  freeCompletionMapWellDefined f fWD {ofInv x} {ofInv x₁} w1=w2 = fWD w1=w2

  record Word {a b : _} {A : Set a} (S : Setoid {a} {b} A) : Set (a ⊔ b) where
    inductive
    field
      length : ℕ
      word : Vec (FreeCompletion S) length

  vecEquality : {a b : _} {A : Set a} (S : Setoid {a} {b} A) {n : ℕ} → Rel {a} {b} (Vec A n)
  (vecEquality S {zero} w1) w2 = True'
  (vecEquality S {succ n} (x ,- w1)) (y ,- w2) = (Setoid._∼_ S x y) && ((vecEquality S) w1 w2)

  vecEqualityReflexive : {a b : _} {A : Set a} (S : Setoid {a} {b} A) {n : ℕ} (w : Vec A n) → vecEquality S w w
  vecEqualityReflexive S [] = record {}
  vecEqualityReflexive S (x ,- w) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S)) ,, vecEqualityReflexive S w

  vecEqualitySymmetric : {a b : _} {A : Set a} (S : Setoid {a} {b} A) {n : ℕ} {w1 w2 : Vec A n} → vecEquality S w1 w2 → vecEquality S w2 w1
  vecEqualitySymmetric S {w1 = []} {[]} pr = record {}
  vecEqualitySymmetric S {w1 = x ,- w1} {y ,- w2} (pr1 ,, pr2) = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S)) pr1 ,, vecEqualitySymmetric S pr2

  vecEqualityTransitive : {a b : _} {A : Set a} (S : Setoid {a} {b} A) {n : ℕ} {w1 w2 w3 : Vec A n} → vecEquality S w1 w2 → vecEquality S w2 w3 → vecEquality S w1 w3
  vecEqualityTransitive S {w1 = []} {w2} {w3} w1=w2 w2=w3 = record {}
  vecEqualityTransitive S {w1 = x ,- w1} {y ,- w2} {z ,- w3} (pr1 ,, pr2) (pr3 ,, pr4) = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S)) pr1 pr3 ,, vecEqualityTransitive S pr2 pr4

  vecEqualityRespectsMap : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) (fWD : {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)) → {m : ℕ} {w1 w2 : Vec A m} (w1=w2 : vecEquality S w1 w2) → vecEquality T (vecMap f w1) (vecMap f w2)
  vecEqualityRespectsMap S T f fWD {zero} {w1} {w2} w1=w2 = record {}
  vecEqualityRespectsMap S T f fWD {succ n} {x ,- w1} {y ,- w2} (x=y ,, snd) = fWD x=y ,, vecEqualityRespectsMap S T f fWD snd

  vecEquality' : {a b : _} {A : Set a} (S : Setoid {a} {b} A) {m n : ℕ} → (Vec A m) → (Vec A n) → Set b
  vecEquality' S {m} {n} w1 w2 with equalityDecidable m n
  vecEquality' S {m} {.m} w1 w2 | inl refl = vecEquality S w1 w2
  vecEquality' S {m} {n} w1 w2 | inr x = False'

  vecEquality'RespectsMap : {a b c d : _} {A : Set a} {B : Set b} (S : Setoid {a} {c} A) (T : Setoid {b} {d} B) (f : A → B) (fWD : {x y : A} → Setoid._∼_ S x y → Setoid._∼_ T (f x) (f y)) → {m n : ℕ} {w1 : Vec A m} {w2 : Vec A n} (w1=w2 : vecEquality' S w1 w2) → vecEquality' T (vecMap f w1) (vecMap f w2)
  vecEquality'RespectsMap S T f fWD {m = m} {n = n} w1=w2 with equalityDecidable m n
  vecEquality'RespectsMap S T f fWD {m} {.m} w1=w2 | inl refl = vecEqualityRespectsMap S T f fWD w1=w2
  vecEquality'RespectsMap S T f fWD {m} {n} () | inr x

  wordSetoid : {a b : _} {A : Set a} (S : Setoid {a} {b} A) → Setoid (Word S)
  (wordSetoid S Setoid.∼ record { length = length1 ; word = word1 }) record { length = length2 ; word = word2 } = vecEquality' (freeCompletionSetoid S) word1 word2
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (wordSetoid S))) {record { length = length ; word = word }} with equalityDecidable length length
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (wordSetoid S))) {record { length = length ; word = word }} | inl refl = vecEqualityReflexive (freeCompletionSetoid S) word
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (wordSetoid S))) {record { length = length ; word = word }} | inr x = exFalso (x refl)
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = length2 ; word = word2 }} pr with equalityDecidable length1 length2
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = .length1 ; word = word2 }} pr | inl refl with equalityDecidable length1 length1
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = .length1 ; word = word2 }} pr | inl refl | inl refl = vecEqualitySymmetric (freeCompletionSetoid S) pr
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = .length1 ; word = word2 }} pr | inl refl | inr x = exFalso (x refl)
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = length2 ; word = word2 }} () | inr x
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = length2 ; word = word2 }} {record { length = length3 ; word = word3 }} pr1 pr2 with equalityDecidable length1 length2
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = .length1 ; word = word2 }} {record { length = length3 ; word = word3 }} pr1 pr2 | inl refl with equalityDecidable length1 length3
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = .length1 ; word = word2 }} {record { length = .length1 ; word = word3 }} pr1 pr2 | inl refl | inl refl = vecEqualityTransitive (freeCompletionSetoid S) pr1 pr2
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = .length1 ; word = word2 }} {record { length = length3 ; word = word3 }} pr1 () | inl refl | inr x
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (wordSetoid S))) {record { length = length1 ; word = word1 }} {record { length = length2 ; word = word2 }} {record { length = length3 ; word = word3 }} () _ | inr x

  --wordRefl : {a b : _} {A : Set a} {S : Setoid {a} {b} A} (w1 w2 : Word S) → (Word.length w1 ≡ Word.length w2) → vecEquality (freeCompletionSetoid S) (Word.word w1) (Word.word w2) → Setoid._∼_ (wordSetoid S) w1 w2
  --wordRefl = ?

  evalWord : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) (w : Word S) → A
  evalWord G record { length = zero ; word = [] } = Group.identity G
  evalWord {_+_ = _+_} G record { length = (succ length) ; word = ((ofLetter x) ,- word) } = x + evalWord G record { length = length ; word = word }
  evalWord {_+_ = _+_} G record { length = (succ length) ; word = ((ofInv x) ,- word) } = (Group.inverse G x) + evalWord G record { length = length ; word = word }

  mapWord : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) (w : Word S) → Word T
  mapWord f record { length = length ; word = word } = record { length = length ; word = vecMap (freeCompletionMap f) word }

  subgroupSetoid : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} (T : Setoid {b} {d} B) {_+_ : A → A → A} (G : Group S _+_) {f : B → A} (fInj : SetoidInjection T S f) → Setoid (Word T)
  Setoid._∼_ (subgroupSetoid {S = S} T G {f} fInj) w1 w2 = Setoid._∼_ S (evalWord G (mapWord f w1)) (evalWord G (mapWord f w2))
  Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq (subgroupSetoid {S = S} T G {f} fInj))) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq (subgroupSetoid {S = S} T G {f} fInj))) = Symmetric.symmetric (Equivalence.symmetricEq (Setoid.eq S))
  Transitive.transitive (Equivalence.transitiveEq (Setoid.eq (subgroupSetoid {S = S} T G {f} fInj))) = Transitive.transitive (Equivalence.transitiveEq (Setoid.eq S))

  evalWordWellDefined : {a b : _} {A : Set a} {S : Setoid {a} {b} A} {_+_ : A → A → A} (G : Group S _+_) (w1 w2 : Word S) → Setoid._∼_ (wordSetoid S) w1 w2 → Setoid._∼_ S (evalWord G w1) (evalWord G w2)
  evalWordWellDefined G record { length = length1 ; word = word1 } record { length = length2 ; word = word2 } w1=w2 with equalityDecidable length1 length2
  evalWordWellDefined {S = S} G record { length = .0 ; word = [] } record { length = .0 ; word = [] } record {} | inl refl = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  evalWordWellDefined {S = S} G record { length = (succ n) ; word = (ofLetter x ,- word1) } record { length = .(succ n) ; word = (ofLetter x₁ ,- word2) } (x=y ,, word1=word2) | inl refl = Group.wellDefined G x=y (evalWordWellDefined G record { length = n ; word = word1 } record { length = n ; word = word2 } needed)
    where
      needed : Setoid._∼_ (wordSetoid S) record { length = n ; word = word1 } record { length = n ; word = word2 }
      needed with equalityDecidable n n
      needed | inl refl = word1=word2
      needed | inr x = exFalso (x refl)
  evalWordWellDefined G record { length = .(succ _) ; word = (ofLetter x ,- word1) } record { length = .(succ _) ; word = (ofInv x₁ ,- word2) } (() ,, word1=word2) | inl refl
  evalWordWellDefined G record { length = .(succ _) ; word = (ofInv x ,- word1) } record { length = .(succ _) ; word = (ofLetter x₁ ,- word2) } (() ,, word1=word2) | inl refl
  evalWordWellDefined {S = S} G record { length = (succ n) ; word = (ofInv x ,- word1) } record { length = .(succ n) ; word = (ofInv x₁ ,- word2) } (x=y ,, word1=word2) | inl refl = Group.wellDefined G (inverseWellDefined G x=y) (evalWordWellDefined G record { length = n ; word = word1 } record { length = n ; word = word2 } needed)
    where
      needed : Setoid._∼_ (wordSetoid S) record { length = n ; word = word1 } record { length = n ; word = word2 }
      needed with equalityDecidable n n
      needed | inl refl = word1=word2
      needed | inr x = exFalso (x refl)
  evalWordWellDefined G record { length = length1 ; word = word1 } record { length = length2 ; word = word2 } () | inr x

  mapWordWellDefined : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} {T : Setoid {b} {d} B} (f : A → B) → ({x y : A} → (Setoid._∼_ S x y) → (Setoid._∼_ T (f x) (f y))) → {w1 : Word S} {w2 : Word S} → Setoid._∼_ (wordSetoid S) w1 w2 → Setoid._∼_ (wordSetoid T) (mapWord f w1) (mapWord f w2)
  mapWordWellDefined {S = S} {T = T} f fWD {w1} {w2} w1=w2 = p
    where
      p : vecEquality' (freeCompletionSetoid T) {m = Word.length w1} {n = Word.length w2} (vecMap (freeCompletionMap {S = S} {T = T} f) (Word.word w1)) (vecMap (freeCompletionMap f) (Word.word w2))
      p = vecEquality'RespectsMap (freeCompletionSetoid S) (freeCompletionSetoid T) (freeCompletionMap {S = S} {T} f) (λ {x} {y} → freeCompletionMapWellDefined {S = S} {T = T} f fWD {x} {y}) {w1 = Word.word w1} {w2 = Word.word w2} w1=w2

  subgroupOp : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} (T : Setoid {b} {d} B) {_+_ : A → A → A} (G : Group S _+_) {f : B → A} (fInj : SetoidInjection T S f) → Word T → Word T → Word T
  subgroupOp T G fInj record { length = length1 ; word = word1 } record { length = length2 ; word = word2 } = record { length = length1 +N length2 ; word = word1 +V word2 }

  generatedSubgroup : {a b c d : _} {A : Set a} {B : Set b} {S : Setoid {a} {c} A} (T : Setoid {b} {d} B) {_+_ : A → A → A} (G : Group S _+_) {f : B → A} (fInj : SetoidInjection T S f) → Group (subgroupSetoid T G fInj) (subgroupOp T G fInj)
  Group.wellDefined (generatedSubgroup T G fInj) = {!!}
  Group.identity (generatedSubgroup T G fInj) = record { length = 0 ; word = [] }
  Group.inverse (generatedSubgroup T G fInj) record { length = length ; word = word } = record { length = length ; word = vecMap freeInverse (vecRev word) }
  Group.multAssoc (generatedSubgroup T G fInj) = {!!}
  Group.multIdentRight (generatedSubgroup {S = S} T G {f = f} fInj) {a = record { length = length ; word = word }} = need
    where
      open Setoid S
      open Group G
      need : evalWord G (mapWord f (record { length = length +N 0 ; word = word +V [] })) ∼ evalWord G (mapWord f record { length = length ; word = word })
      need = evalWordWellDefined G (mapWord f (record { length = length +N 0 ; word = word +V [] })) (mapWord f record { length = length ; word = word }) p
        where
          q : Setoid._∼_ (wordSetoid T) (record { length = length +N 0 ; word = word +V [] }) (record { length = length ; word = word })
          q = {!!}
          p : Setoid._∼_ (wordSetoid S) (mapWord f (record { length = length +N 0 ; word = word +V [] })) (mapWord f record { length = length ; word = word })
          p = mapWordWellDefined {T = {!freeCompletionSetoid S!}} f (SetoidInjection.wellDefined fInj) q
  Group.multIdentLeft (generatedSubgroup {S = S} T G {f = f} fInj) = Reflexive.reflexive (Equivalence.reflexiveEq (Setoid.eq S))
  Group.invLeft (generatedSubgroup {S = S} T G {f = f} fInj) {w} = need
    where
      open Setoid S
      open Group G
      need : evalWord G (mapWord f {!!}) ∼ identity
      need = {!!}
  Group.invRight (generatedSubgroup T G fInj) = {!!}
