{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Numbers.Naturals -- for length
open import Lists.Lists
open import Orders
open import Functions
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Groups.FinitePermutations

module Lists.SortList where
  isSorted : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) (l : List A) → Set (a ⊔ b)
  isSorted ord [] = True'
  isSorted ord (x :: []) = True'
  isSorted ord (x :: (y :: l)) = (TotalOrder._≤_ ord x y) && (isSorted ord (y :: l))

  sortedTailIsSorted : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → (x : A) → (l : List A) → (isSorted ord (x :: l)) → isSorted ord l
  sortedTailIsSorted ord x [] pr = record {}
  sortedTailIsSorted ord x (y :: l) (fst ,, snd) = snd

  insert : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → (l : List A) → (isSorted ord l) → (x : A) → List A
  insert ord [] pr x = [ x ]
  insert ord (y :: l) pr x with TotalOrder.totality ord x y
  insert ord (y :: l) pr x | inl (inl x<y) = x :: (y :: l)
  insert ord (y :: l) pr x | inl (inr y<x) = y :: insert ord l (sortedTailIsSorted ord y l pr) x
  insert ord (y :: l) pr x | inr x=y = x :: (y :: l)

  insertionIncreasesLength : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → (l : List A) → (x : A) → (pr : isSorted ord l) → length (insert ord l pr x) ≡ succ (length l)
  insertionIncreasesLength ord [] x pr = refl
  insertionIncreasesLength ord (y :: l) x pr with TotalOrder.totality ord x y
  insertionIncreasesLength ord (y :: l) x pr | inl (inl x<y) = refl
  insertionIncreasesLength ord (y :: l) x pr | inl (inr y<x) = applyEquality succ (insertionIncreasesLength ord l x (sortedTailIsSorted ord y l pr))
  insertionIncreasesLength ord (y :: l) x pr | inr x=y = refl

  isEmpty : {a : _} {A : Set a} (l : List A) → Bool
  isEmpty [] = BoolTrue
  isEmpty (x :: l) = BoolFalse

  minList : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → (l : List A) → (isEmpty l ≡ BoolFalse) → A
  minList ord [] ()
  minList ord (x :: []) pr = x
  minList ord (x :: (y :: l)) refl with minList ord (y :: l) refl
  minList ord (x :: (y :: l)) refl | minSoFar with TotalOrder.totality ord x minSoFar
  minList ord (x :: (y :: l)) refl | minSoFar | inl (inl x<m) = x
  minList ord (x :: (y :: l)) refl | minSoFar | inl (inr m<x) = minSoFar
  minList ord (x :: (y :: l)) refl | minSoFar | inr x=m = x

  insertionSorts : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → (l : List A) → (pr : isSorted ord l) → (x : A) → isSorted ord (insert ord l pr x)
  insertionSorts ord [] _ _ = record {}
  insertionSorts ord (y :: l) pr x with TotalOrder.totality ord x y
  insertionSorts ord (y :: l) pr x | inl (inl x<y) = inl x<y ,, pr
  insertionSorts ord (y :: l) pr x | inl (inr y<x) with insertionSorts ord l (sortedTailIsSorted ord y l pr) x
  ... | bl = {!!}
  insertionSorts ord (y :: l) pr x | inr x=y = inr x=y ,, pr

  orderNotLessThanAndEqual : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → {x y : A} → (x ≡ y) → TotalOrder._<_ ord x y → False
  orderNotLessThanAndEqual ord {x} {y} x=y x<y rewrite x=y = PartialOrder.irreflexive (TotalOrder.order ord) x<y

  orderToDecidableEquality : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → {x y : A} → (x ≡ y) || ((x ≡ y) → False)
  orderToDecidableEquality ord {x} {y} with TotalOrder.totality ord x y
  orderToDecidableEquality ord {x} {y} | inl (inl x<y) = inr λ x=y → orderNotLessThanAndEqual ord x=y x<y
  orderToDecidableEquality ord {x} {y} | inl (inr y<x) = inr λ x=y → orderNotLessThanAndEqual ord (equalityCommutative x=y) y<x
  orderToDecidableEquality ord {x} {y} | inr x=y = inl x=y

  --SortingAlgorithm : {a b : _} → Set (lsuc a ⊔ lsuc b)
  --SortingAlgorithm {a} {b} = {A : Set a} → (ord : TotalOrder {a} {b} A) → (input : List A) → Sg (List A) (λ l → isSorted ord l && isPermutation (orderToDecidableEquality ord) l input)

  insertionSort : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) (l : List A) → List A
  insertionSortIsSorted : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) (l : List A) → isSorted ord (insertionSort ord l)

  insertionSort ord [] = []
  insertionSort ord (x :: l) = insert ord (insertionSort ord l) (insertionSortIsSorted ord l) x
  insertionSortIsSorted ord [] = record {}
  insertionSortIsSorted ord (x :: l) = insertionSorts ord (insertionSort ord l) (insertionSortIsSorted ord l) x

  insertionSortLength : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) (l : List A) → length l ≡ length (insertionSort ord l)
  insertionSortLength ord [] = refl
  insertionSortLength ord (x :: l) rewrite insertionIncreasesLength ord (insertionSort ord l) x (insertionSortIsSorted ord l) = applyEquality succ (insertionSortLength ord l)

  isPermutation : {a b : _} {A : Set a} (ord : TotalOrder {a} {b} A) → (l m : List A) → Set a
  isPermutation ord l m = insertionSort ord l ≡ insertionSort ord m

  --insertionSort : {a b : _} → SortingAlgorithm {a} {b}
  --insertionSort {A = A} ord l = {!!}
  --  where
  --    lemma : Sg (List A) (isSorted ord) → (x : A) → Sg (List A) (isSorted ord)
  --    lemma (l , b) x = insert ord l b x , insertionSorts ord l b x

  --InsertionSort : {a b : _} → SortingAlgorithm {a} {b}
  --InsertionSort ord l = insertionSort ord l

  lexicographicOrderRel : {a b : _} {A : Set a} → (TotalOrder {a} {b} A) → Rel {a} {a ⊔ b} (List A)
  lexicographicOrderRel _ [] [] = False'
  lexicographicOrderRel _ [] (x :: l2) = True'
  lexicographicOrderRel _ (x :: l1) [] = False'
  lexicographicOrderRel order (x :: l1) (y :: l2) = (TotalOrder._<_ order x y) || ((x ≡ y) && lexicographicOrderRel order l1 l2)

  lexIrrefl : {a b : _} {A : Set a} (o : TotalOrder {a} {b} A) → {x : List A} → lexicographicOrderRel o x x → False
  lexIrrefl o {[]} ()
  lexIrrefl o {x :: l} (inl x<x) = PartialOrder.irreflexive (TotalOrder.order o) x<x
  lexIrrefl o {x :: l} (inr (refl ,, l=l)) = lexIrrefl o {l} l=l

  lexTransitive : {a b : _} {A : Set a} (o : TotalOrder {a} {b} A) → {x y z : List A} → lexicographicOrderRel o x y → lexicographicOrderRel o y z → lexicographicOrderRel o x z
  lexTransitive o {[]} {[]} {z} x<y y<z = y<z
  lexTransitive o {[]} {x :: y} {[]} record {} y<z = y<z
  lexTransitive o {[]} {x :: y} {x₁ :: z} record {} y<z = record {}
  lexTransitive o {x :: xs} {[]} {z} () y<z
  lexTransitive o {x :: xs} {y :: ys} {[]} (inl x<y) ()
  lexTransitive o {x :: xs} {y :: ys} {z :: zs} (inl x<y) (inl y<z) = inl (PartialOrder.transitive (TotalOrder.order o) x<y y<z)
  lexTransitive o {x :: xs} {y :: ys} {.y :: zs} (inl x<y) (inr (refl ,, ys<zs)) = inl x<y
  lexTransitive o {x :: xs} {.x :: ys} {[]} (inr (refl ,, xs<ys)) ()
  lexTransitive o {x :: xs} {.x :: ys} {z :: zs} (inr (refl ,, xs<ys)) (inl y<z) = inl y<z
  lexTransitive o {x :: xs} {.x :: ys} {.x :: zs} (inr (refl ,, xs<ys)) (inr (refl ,, u)) = inr (refl ,, lexTransitive o xs<ys u)

  lexTotal : {a b : _} {A : Set a} (o : TotalOrder {a} {b} A) → (x y : List A) → ((lexicographicOrderRel o x y) || (lexicographicOrderRel o y x)) || (x ≡ y)
  lexTotal o [] [] = inr refl
  lexTotal o [] (x :: y) = inl (inl (record {}))
  lexTotal o (x :: xs) [] = inl (inr (record {}))
  lexTotal o (x :: xs) (y :: ys) with TotalOrder.totality o x y
  lexTotal o (x :: xs) (y :: ys) | inl (inl x<y) = inl (inl (inl x<y))
  lexTotal o (x :: xs) (y :: ys) | inl (inr y<x) = inl (inr (inl y<x))
  lexTotal o (x :: xs) (y :: ys) | inr x=y with lexTotal o xs ys
  lexTotal o (x :: xs) (y :: ys) | inr x=y | inl (inl xs<ys) = inl (inl (inr (x=y ,, xs<ys)))
  lexTotal o (x :: xs) (y :: ys) | inr x=y | inl (inr ys<xs) = inl (inr (inr (equalityCommutative x=y ,, ys<xs)))
  lexTotal o (x :: xs) (y :: ys) | inr x=y | inr xs=ys rewrite x=y | xs=ys = inr refl

  lexicographicOrder : {a b : _} {A : Set a} → (TotalOrder {a} {b} A) → TotalOrder (List A)
  PartialOrder._<_ (TotalOrder.order (lexicographicOrder order)) = lexicographicOrderRel order
  PartialOrder.irreflexive (TotalOrder.order (lexicographicOrder order)) = lexIrrefl order
  PartialOrder.transitive (TotalOrder.order (lexicographicOrder order)) = lexTransitive order
  TotalOrder.totality (lexicographicOrder order) = lexTotal order

  badSort : {a b : _} {A : Set a} (order : TotalOrder {a} {b} A) → ℕ → List A → List A
  badSortLength : {a b : _} {A : Set a} (order : TotalOrder {a} {b} A) → (n : ℕ) → (l : List A) → length (badSort order n l) ≡ length l
  allTrueRespectsBadsort : {a b c : _} {A : Set a} (order : TotalOrder {a} {b} A) → (n : ℕ) → (l : List A) → (pred : A → Set c) → allTrue pred l → allTrue pred (badSort order n l)

  badSort order zero = insertionSort order
  badSort order (succ n) [] = []
  badSort {A = A} order (succ n) (x :: l) = head (badSort (lexicographicOrder order) n (permutations (x :: l))) bsNonempty
    where
      bs : List (List A)
      bs = badSort (lexicographicOrder order) n (permutations (x :: l))
      bsNonempty : 0 <N length bs
      bsNonempty with bs
      bsNonempty | [] = {!!}
      bsNonempty | bl :: _ = succIsPositive _

  allTrueRespectsBadsort order n [] pred record {} = {!!}
  allTrueRespectsBadsort order n (x :: l) pred (fst ,, snd) = ?
  badSortLength order zero [] = refl
  badSortLength order zero (x :: l) = transitivity (insertionIncreasesLength order (insertionSort order l) x (insertionSortIsSorted order l)) (applyEquality succ (equalityCommutative (insertionSortLength order l)))
  badSortLength order (succ n) [] = refl
  badSortLength order (succ n) (x :: l) = {!!}
    where
      allLen : allTrue (λ i → length i ≡ succ (length l)) (badSort (lexicographicOrder order) n (flatten (map (allInsertions x) (permutations l))))
      allLen = {!!}

-- TODO: show that insertion sort actually produces a permutation
