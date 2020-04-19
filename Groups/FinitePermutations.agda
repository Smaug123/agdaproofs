{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Numbers.Naturals.Semiring -- for length
open import Lists.Lists
open import Functions.Definition
--open import Groups.Actions

module Groups.FinitePermutations where

allInsertions : {a : _} {A : Set a} (x : A) (l : List A) → List (List A)
allInsertions x [] = [ x ] :: []
allInsertions x (y :: l) = (x :: (y :: l)) :: (map (λ i → y :: i) (allInsertions x l))

permutations : {a : _} {A : Set a} (l : List A) → List (List A)
permutations [] = [ [] ]
permutations (x :: l) = flatten (map (allInsertions x) (permutations l))

factorial : ℕ → ℕ
factorial zero = 1
factorial (succ n) = (succ n) *N factorial n

factCheck : factorial 5 ≡ 120
factCheck = refl

allInsertionsLength : {a : _} {A : Set a} (x : A) (l : List A) → length (allInsertions x l) ≡ succ (length l)
allInsertionsLength x [] = refl
allInsertionsLength x (y :: l) = applyEquality succ (transitivity (equalityCommutative (lengthMap (allInsertions x l) {f = y ::_})) (allInsertionsLength x l))

allInsertionsLength' : {a : _} {A : Set a} (x : A) (l : List A) → allTrue (λ i → length i ≡ succ (length l)) (allInsertions x l)
allInsertionsLength' x [] = refl ,, record {}
allInsertionsLength' x (y :: l) with allInsertionsLength' x l
... | bl = refl ,, allTrueMap (λ i → length i ≡ succ (succ (length l))) (y ::_) (allInsertions x l) (allTrueExtension (λ z → length z ≡ succ (length l)) ((λ i → length i ≡ succ (succ (length l))) ∘ (y ::_)) (allInsertions x l) (λ {x} → λ p → applyEquality succ p) bl)

permutationsCheck : permutations (3 :: 4 :: []) ≡ (3 :: 4 :: []) :: (4 :: 3 :: []) :: []
permutationsCheck = refl

permsAllSameLength : {a : _} {A : Set a} (l : List A) → allTrue (λ i → length i ≡ length l) (permutations l)
permsAllSameLength [] = refl ,, record {}
permsAllSameLength (x :: l) with permsAllSameLength l
... | bl = allTrueFlatten (λ i → length i ≡ succ (length l)) (map (allInsertions x) (permutations l)) (allTrueMap (allTrue (λ i → length i ≡ succ (length l))) (allInsertions x) (permutations l) (allTrueExtension (λ z → length z ≡ length l) (allTrue (λ i → length i ≡ succ (length l)) ∘ allInsertions x) (permutations l) lemma bl))
  where
    lemma : {m : List _} → (lenM=lenL : length m ≡ length l) → allTrue (λ i → length i ≡ succ (length l)) (allInsertions x m)
    lemma {m} lm=ll rewrite equalityCommutative lm=ll = allInsertionsLength' x m

allTrueEqual : {a b : _} {A : Set a} {B : Set b} (f : A → B) (equalTo : B) (l : List A) → allTrue (λ i → f i ≡ equalTo) l → map f l ≡ replicate (length l) equalTo
allTrueEqual f equalTo [] pr = refl
allTrueEqual f equalTo (x :: l) (fst ,, snd) rewrite fst | allTrueEqual f equalTo l snd = refl

totalReplicate : (l len : ℕ) → fold _+N_ 0 (replicate len l) ≡ l *N len
totalReplicate l zero rewrite multiplicationNIsCommutative l 0 = refl
totalReplicate l (succ len) rewrite totalReplicate l len | multiplicationNIsCommutative l (succ len) = applyEquality (l +N_) (multiplicationNIsCommutative l len)

permsLen : {a : _} {A : Set a} (l : List A) → length (permutations l) ≡ factorial (length l)
permsLen [] = refl
permsLen (x :: l) = transitivity (lengthFlatten (map (allInsertions x) (permutations l))) (transitivity (applyEquality (fold _+N_ 0) (mapMap (permutations l))) (transitivity (applyEquality (fold _+N_ 0) (mapExtension (permutations l) (length ∘ allInsertions x) (succ ∘ length) λ {y} → allInsertionsLength x y)) (transitivity (applyEquality (fold _+N_ 0) lemma) (transitivity (totalReplicate (succ (length l)) (length (permutations l))) ans))))
  where
    lemma : map (λ a → succ (length a)) (permutations l) ≡ replicate (length (permutations l)) (succ (length l))
    lemma = allTrueEqual (λ a → succ (length a)) (succ (length l)) (permutations l) (allTrueExtension (λ z → length z ≡ length l) (λ i → succ (length i) ≡ succ (length l)) (permutations l) (λ pr → applyEquality succ pr) (permsAllSameLength l))
    ans : length (permutations l) +N length l *N length (permutations l) ≡ factorial (length l) +N length l *N factorial (length l)
    ans rewrite permsLen l = refl

--act : GroupAction (symmetricGroup (symmetricSetoid (reflSetoid (FinSet n))))
--act = ?

{- TODO: show that symmetricGroup acts in the obvious way on permutations FinSet
listElements : {a : _} {A : Set a} (l : List A) → Set
listElements [] = False
listElements (x :: l) = True || listElements l

listElement : {a : _} {A : Set a} {l : List A} (elt : listElements l) → A
listElement {l = []} ()
listElement {l = x :: l} (inl record {}) = x
listElement {l = x :: l} (inr elt) = listElement {l = l} elt

backwardRange : ℕ → List ℕ
backwardRange zero = []
backwardRange (succ n) = n :: backwardRange n

backwardRangeLength : {n : ℕ} → length (backwardRange n) ≡ n
backwardRangeLength {zero} = refl
backwardRangeLength {succ n} rewrite backwardRangeLength {n} = refl

applyPermutation : {n : ℕ} → (f : FinSet n → FinSet n) → listElements (permutations (backwardRange n)) → listElements (permutations (backwardRange n))
applyPermutation {zero} f (inl record {}) = inl (record {})
applyPermutation {zero} f (inr ())
applyPermutation {succ n} f elt = {!!}

finitePermutations : (n : ℕ) → SetoidToSet (symmetricSetoid (reflSetoid (FinSet n))) (listElements (permutations (backwardRange n)))
SetoidToSet.project (finitePermutations n) (sym {f} fBij) = {!!}
SetoidToSet.wellDefined (finitePermutations n) = {!!}
SetoidToSet.surj (finitePermutations n) = {!!}
SetoidToSet.inj (finitePermutations n) = {!!}

-}
