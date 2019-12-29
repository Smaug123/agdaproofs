{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Orders.Total.Definition
open import Orders.Total.Lemmas
open import Maybe
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Vectors

open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order

module KeyValue.LinearStore.Implementation {a b c} (keySet : Set a) (valueSet : Set b) (keyOrder : TotalOrder {_} keySet {c}) where

record ReducedMap (min : keySet) : Set (a ⊔ b ⊔ c)
record ReducedMap min where
  inductive
  field
    firstEntry : valueSet
    next : Maybe (Sg keySet (λ nextKey → (ReducedMap nextKey) && (TotalOrder._<_ keyOrder min nextKey)))

addReducedMap : {min : keySet} → (k : keySet) → (v : valueSet) → (m : ReducedMap min) → ReducedMap (TotalOrder.min keyOrder min k)
addReducedMap {min} k v m with TotalOrder.totality keyOrder min k
addReducedMap {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) = record { firstEntry = firstEntry ; next = yes (k , (record { firstEntry = v ; next = no} ,, min<k))}
addReducedMap {min} k v record { firstEntry = minVal ; next = yes (nextKey , (m ,, pr)) } | inl (inl min<k) = record { firstEntry = minVal ; next = yes ((TotalOrder.min keyOrder nextKey k) , (addReducedMap {_} k v m ,, minFromBoth keyOrder pr min<k))}
addReducedMap {min} k v record { firstEntry = firstEntry ; next = next } | inl (inr k<min) = record { firstEntry = v ; next = yes (min , (record { firstEntry = firstEntry ; next = next } ,, k<min)) }
addReducedMap {min} k v record { firstEntry = firstEntry ; next = next } | inr min=k rewrite min=k = record { firstEntry = v ; next = next }

lookupReduced : {min : keySet} → (m : ReducedMap min) → (target : keySet) → Maybe valueSet
lookupReduced {min} m k with TotalOrder.totality keyOrder min k
lookupReduced {min} record { firstEntry = firstEntry ; next = no } k | inl (inl min<k) = no
lookupReduced {min} record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, _))) } k | inl (inl min<k) = lookupReduced {newMin} m k
lookupReduced {min} m k | inl (inr k<min) = no
lookupReduced {min} record { firstEntry = firstEntry ; next = next } k | inr min=k = yes firstEntry

countReduced : {min : keySet} → (m : ReducedMap min) → ℕ
countReduced record { firstEntry = firstEntry ; next = no } = 1
countReduced record { firstEntry = firstEntry ; next = (yes (key , (m ,, pr))) } = succ (countReduced m)

lookupReducedSucceedsAfterAdd : {min : keySet} → (k : keySet) → (v : valueSet) → (m : ReducedMap min) → (lookupReduced (addReducedMap k v m) k ≡ yes v)
lookupReducedSucceedsAfterAdd {min} k v m with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) with TotalOrder.totality keyOrder k k
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) | inl (inl k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) | inl (inr k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) | inr p = refl
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inr k<min) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder min<k k<min))
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inr min=k rewrite min=k = exFalso (TotalOrder.irreflexive keyOrder min<k)
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) | inl (inl _) = lookupReducedSucceedsAfterAdd k v m
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) | inl (inr k<min) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder min<k k<min))
lookupReducedSucceedsAfterAdd {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) | inr min=k rewrite min=k = exFalso (TotalOrder.irreflexive keyOrder min<k)
lookupReducedSucceedsAfterAdd {min} k v m | inl (inr k<min) with TotalOrder.totality keyOrder k k
lookupReducedSucceedsAfterAdd {min} k v m | inl (inr k<min) | inl (inl k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
lookupReducedSucceedsAfterAdd {min} k v m | inl (inr k<min) | inl (inr k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
lookupReducedSucceedsAfterAdd {min} k v m | inl (inr k<min) | inr p = refl
lookupReducedSucceedsAfterAdd {min} k v m | inr min=k with TotalOrder.totality keyOrder k k
lookupReducedSucceedsAfterAdd {min} k v m | inr min=k | inl (inl k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
lookupReducedSucceedsAfterAdd {min} k v m | inr min=k | inl (inr k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
lookupReducedSucceedsAfterAdd {min} k v m | inr min=k | inr p with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterAdd {min} k v m | inr min=k | inr p | inl (inl min<k) rewrite min=k = exFalso (TotalOrder.irreflexive keyOrder min<k)
lookupReducedSucceedsAfterAdd {min} k v m | inr min=k | inr p | inl (inr k<min) rewrite min=k = exFalso (TotalOrder.irreflexive keyOrder k<min)
lookupReducedSucceedsAfterAdd {.k} k v record { firstEntry = firstEntry ; next = next } | inr refl | inr p | inr s = refl

lookupReducedSucceedsAfterUnrelatedAdd : {min : keySet} → (unrelatedK : keySet) → (unrelatedV : valueSet) → (k : keySet) → (v : valueSet) → ((TotalOrder._<_ keyOrder unrelatedK k) || (TotalOrder._<_ keyOrder k unrelatedK)) → (m : ReducedMap min) → (lookupReduced m k ≡ yes v) → lookupReduced (addReducedMap unrelatedK unrelatedV m) k ≡ yes v
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m lookupReducedSucceeds with TotalOrder.totality keyOrder min k'
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m lookupReducedSucceeds | inl (inl min<k') with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr record { firstEntry = firstEntry ; next = no } () | inl (inl min<k') | inl (inl min<k)
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedSucceeds | inl (inl min<k') | inl (inl min<k) = lookupReducedSucceedsAfterUnrelatedAdd {a} k' v' k v pr fst lookupReducedSucceeds
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inl x) m lookupReducedSucceeds | inl (inl min<k') | inl (inr k<min) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder k<min (TotalOrder.<Transitive keyOrder min<k' x)))
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inr k<k') m () | inl (inl min<k') | inl (inr k<min)
lookupReducedSucceedsAfterUnrelatedAdd {.min} k' v' min v (inl x) m lookupReducedSucceeds | inl (inl min<k') | inr refl = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder x min<k'))
lookupReducedSucceedsAfterUnrelatedAdd {.min} k' v' min v (inr x) record { firstEntry = v2 ; next = no } p | inl (inl min<k') | inr refl = applyEquality yes (yesInjective p)
lookupReducedSucceedsAfterUnrelatedAdd {.min} k' v' min v (inr x) record { firstEntry = .v ; next = (yes (a , b)) } refl | inl (inl min<k') | inr refl = applyEquality yes refl
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) with TotalOrder.totality keyOrder k' k
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) | inl (inl k'<k) with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) | inl (inl k'<k) | inl (inl min<k) = lookupReducedSucceeds
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m () | inl (inr k'<min) | inl (inl k'<k) | inl (inr k<min)
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) | inl (inl k'<k) | inr refl = lookupReducedSucceeds
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inl x) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder x k<k'))
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inr x) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inr _) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') | inl (inl x) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder x (TotalOrder.<Transitive keyOrder k<k' k'<min)))
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inr _) m () | inl (inr k'<min) | inl (inr k<k') | inl (inr x)
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inr _) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') | inr x rewrite x = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder k<k' k'<min))
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inl x) m lookupReducedSucceeds | inl (inr k'<min) | inr k'=k rewrite k'=k = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v (inr x) m lookupReducedSucceeds | inl (inr k'<min) | inr k'=k rewrite k'=k = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedSucceedsAfterUnrelatedAdd {min} k' v' k v pr m lookupReducedSucceeds | inr refl with TotalOrder.totality keyOrder min k
lookupReducedSucceedsAfterUnrelatedAdd {k'} k' v' k v (inl _) record { firstEntry = firstEntry ; next = no } () | inr refl | inl (inl min<k)
lookupReducedSucceedsAfterUnrelatedAdd {k'} k' v' k v (inl _) record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedSucceeds | inr refl | inl (inl min<k) = lookupReducedSucceeds
lookupReducedSucceedsAfterUnrelatedAdd {k'} k' v' k v (inr x) m lookupReducedSucceeds | inr refl | inl (inl min<k) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder min<k x))
lookupReducedSucceedsAfterUnrelatedAdd {k'} k' v' k v (inl x) m () | inr refl | inl (inr k<min)
lookupReducedSucceedsAfterUnrelatedAdd {k'} k' v' k v (inr x) m () | inr refl | inl (inr k<min)
lookupReducedSucceedsAfterUnrelatedAdd {.min} .min v' min v (inl x) m lookupReducedSucceeds | inr refl | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedSucceedsAfterUnrelatedAdd {.min} .min v' min v (inr x) m lookupReducedSucceeds | inr refl | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)

lookupReducedFailsAfterUnrelatedAdd : {min : keySet} → (unrelatedK : keySet) → (unrelatedV : valueSet) → (k : keySet) → ((TotalOrder._<_ keyOrder unrelatedK k) || (TotalOrder._<_ keyOrder k unrelatedK)) → (m : ReducedMap min) → (lookupReduced m k ≡ no) → lookupReduced (addReducedMap unrelatedK unrelatedV m) k ≡ no
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr m lookupReducedFails with TotalOrder.totality keyOrder min k'
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr m lookupReducedFails | inl (inl min<k') with TotalOrder.totality keyOrder min k
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) with TotalOrder.totality keyOrder k' k
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inl (inl x) = refl
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inl (inr x) = refl
lookupReducedFailsAfterUnrelatedAdd {min} .k v' k (inl x) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedFailsAfterUnrelatedAdd {min} .k v' k (inr x) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedFails | inl (inl min<k') | inl (inl min<k) = lookupReducedFailsAfterUnrelatedAdd k' v' k pr fst lookupReducedFails
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr m lookupReducedFails | inl (inl min<k') | inl (inr k<min) = refl
lookupReducedFailsAfterUnrelatedAdd {.min} k' v' min pr m () | inl (inl min<k') | inr refl
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr m lookupReducedFails | inl (inr k'<min) with TotalOrder.totality keyOrder min k
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) with TotalOrder.totality keyOrder k' k
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) with TotalOrder.totality keyOrder min k
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inl x₁) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = refl
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inl x₁) record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = lookupReducedFails
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inr x₁) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = refl
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inr x₁) record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = lookupReducedFails
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inr x) = refl
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inr refl = exFalso (TotalOrder.irreflexive keyOrder min<k)
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inr k<k') = refl
lookupReducedFailsAfterUnrelatedAdd {min} .k v' k (inl x) record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedFailsAfterUnrelatedAdd {min} .k v' k (inr x) record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) with TotalOrder.totality keyOrder k' k
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) with TotalOrder.totality keyOrder min k
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) | inl (inl min<k) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder k<min min<k))
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) | inl (inr k<min') = refl
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) | inr refl = exFalso (TotalOrder.irreflexive keyOrder k<min)
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k (inr x) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder k'<k x))
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inr k<k') = refl
lookupReducedFailsAfterUnrelatedAdd {min} .k v' k (inl x) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedFailsAfterUnrelatedAdd {min} .k v' k (inr x) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inr refl = exFalso (TotalOrder.irreflexive keyOrder x)
lookupReducedFailsAfterUnrelatedAdd {min} k' v' k pr m () | inl (inr k'<min) | inr min=k
lookupReducedFailsAfterUnrelatedAdd {min} .min v' k pr m lookupReducedFails | inr refl with TotalOrder.totality keyOrder min k
lookupReducedFailsAfterUnrelatedAdd {min} .min v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inr refl | inl (inl min<k) = refl
lookupReducedFailsAfterUnrelatedAdd {min} .min v' k pr record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedFails | inr refl | inl (inl min<k) = lookupReducedFails
lookupReducedFailsAfterUnrelatedAdd {min} .min v' k pr m lookupReducedFails | inr refl | inl (inr k<min) = refl
lookupReducedFailsAfterUnrelatedAdd {min} .min v' k pr m () | inr refl | inr min=k

countReducedBehavesWhenAddingNotPresent : {min : keySet} → (k : keySet) → (v : valueSet) → (m : ReducedMap min) → (lookupReduced m k ≡ no) → countReduced (addReducedMap k v m) ≡ succ (countReduced m)
countReducedBehavesWhenAddingNotPresent {min} k v m lookupReducedFails with TotalOrder.totality keyOrder k min
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) with TotalOrder.totality keyOrder min k
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) | inl (inl min<k) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder min<k k<min))
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) | inl (inr _) = refl
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) | inr refl = exFalso (TotalOrder.irreflexive keyOrder k<min)
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr min<k) with TotalOrder.totality keyOrder min k
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inr min<k) | inl (inl _) = refl
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedFails | inl (inr min<k) | inl (inl _) = applyEquality succ (countReducedBehavesWhenAddingNotPresent k v (_&&_.fst b) lookupReducedFails)
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr min<k) | inl (inr k<min) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder min<k k<min))
countReducedBehavesWhenAddingNotPresent {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr min<k) | inr refl = exFalso (TotalOrder.irreflexive keyOrder min<k)
countReducedBehavesWhenAddingNotPresent {min} k v m lookupReducedFails | inr refl with TotalOrder.totality keyOrder min min
countReducedBehavesWhenAddingNotPresent {k} k v m lookupReducedFails | inr refl | inl (inl min<min) = exFalso (TotalOrder.irreflexive keyOrder min<min)
countReducedBehavesWhenAddingNotPresent {k} k v m lookupReducedFails | inr refl | inl (inr min<min) = exFalso (TotalOrder.irreflexive keyOrder min<min)
countReducedBehavesWhenAddingNotPresent {k} k v record { firstEntry = firstEntry ; next = no } () | inr refl | inr p
countReducedBehavesWhenAddingNotPresent {k} k v record { firstEntry = firstEntry ; next = (yes x) } () | inr refl | inr p

countReducedBehavesWhenAddingPresent : {min : keySet} → (k : keySet) → (v v' : valueSet) → (m : ReducedMap min) → (lookupReduced m k ≡ yes v') → countReduced (addReducedMap k v m) ≡ countReduced m
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds with TotalOrder.totality keyOrder k min
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inl (inl k<min) with TotalOrder.totality keyOrder min k
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inl (inl k<min) | inl (inl min<k) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder k<min min<k))
countReducedBehavesWhenAddingPresent {min} k v v' m () | inl (inl k<min) | inl (inr _)
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inl (inl k<min) | inr q = exFalso (TotalOrder.irreflexive keyOrder (identityOfIndiscernablesLeft (TotalOrder._<_ keyOrder) k<min (equalityCommutative q)))
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inl (inr min<k) with TotalOrder.totality keyOrder min k
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = no } () | inl (inr min<k) | inl (inl _)
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedSucceeds | inl (inr min<k) | inl (inl _) = applyEquality succ (countReducedBehavesWhenAddingPresent k v v' fst lookupReducedSucceeds)
countReducedBehavesWhenAddingPresent {min} k v v' m () | inl (inr min<k) | inl (inr k<min)
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inl (inr min<k) | inr q = exFalso (TotalOrder.irreflexive keyOrder (identityOfIndiscernablesLeft (λ a b → TotalOrder._<_ keyOrder a b) min<k q))
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inr q with TotalOrder.totality keyOrder min min
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inr q | inl (inl x) = exFalso (TotalOrder.irreflexive keyOrder x)
countReducedBehavesWhenAddingPresent {min} k v v' m lookupReducedSucceeds | inr q | inl (inr x) = exFalso (TotalOrder.irreflexive keyOrder x)
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = no } lookupReducedSucceeds | inr _ | inr p with TotalOrder.totality keyOrder min k
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = no } () | inr _ | inr p | inl (inl x)
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = no } () | inr _ | inr p | inl (inr x`)
countReducedBehavesWhenAddingPresent {.k} k v v' record { firstEntry = firstEntry ; next = no } lookupReducedSucceeds | inr q | inr p | inr refl = refl
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedSucceeds | inr q | inr p with TotalOrder.totality keyOrder k k
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedSucceeds | inr q | inr p | inl (inl x) = exFalso (TotalOrder.irreflexive keyOrder x)
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedSucceeds | inr q | inr p | inl (inr x) = exFalso (TotalOrder.irreflexive keyOrder x)
countReducedBehavesWhenAddingPresent {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , (m ,, pr))) } q | inr q1 | inr p | inr x with TotalOrder.totality keyOrder min k
countReducedBehavesWhenAddingPresent {.k} k v v' record { firstEntry = firstEntry ; next = (yes (a , (m ,, pr))) } q | inr refl | inr p | inr x | inl (inl min<k) = exFalso (TotalOrder.irreflexive keyOrder min<k)
countReducedBehavesWhenAddingPresent {.k} k v v' record { firstEntry = firstEntry ; next = (yes (a , (m ,, pr))) } q | inr q1 | inr p | inr x | inr refl = refl

data Map : Set (a ⊔ b ⊔ c) where
  empty : Map
  nonempty : {min : keySet} → ReducedMap min → Map

addMap : (m : Map) → (k : keySet) → (v : valueSet) → Map
addMap empty k v = nonempty {min = k} record { firstEntry = v ; next = no }
addMap (nonempty x) k v = nonempty (addReducedMap k v x)

lookup : (m : Map) → (target : keySet) → Maybe valueSet
lookup empty t = no
lookup (nonempty x) t = lookupReduced x t

count : (m : Map) → ℕ
count empty = 0
count (nonempty x) = countReduced x

keysReduced : {min : keySet} → (m : ReducedMap min) → Vec keySet (countReduced m)
keysReduced {min = min} record { firstEntry = firstEntry ; next = no } = min ,- []
keysReduced {min = min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } = min ,- (keysReduced fst)

keys : (m : Map) → Vec keySet (count m)
keys empty = []
keys (nonempty m) = keysReduced m

lookupReducedWhenLess : {min : keySet} → (m : ReducedMap min) → (k : keySet) → (TotalOrder._<_ keyOrder k min) → (lookupReduced m k ≡ no)
lookupReducedWhenLess {min} m k k<min with TotalOrder.totality keyOrder min k
lookupReducedWhenLess {min} m k k<min | inl (inl min<k) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder k<min min<k))
lookupReducedWhenLess {min} m k k<min | inl (inr _) = refl
lookupReducedWhenLess {min} m k k<min | inr min=k rewrite min=k = exFalso (TotalOrder.irreflexive keyOrder k<min)

lookupCertainReduced : {min : keySet} → (m : ReducedMap min) → (k : keySet) → (vecContains (keysReduced m) k) → Sg valueSet (λ v → lookupReduced m k ≡ yes v)
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = no } k pr = firstEntry , q
  where
    t : min ≡ k
    t = vecSolelyContains k pr
    q : lookupReduced {min} (record { firstEntry = firstEntry ; next = no }) k ≡ yes firstEntry
    q with TotalOrder.totality keyOrder k k
    q | inl (inl k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
    q | inl (inr k<k) = exFalso (TotalOrder.irreflexive keyOrder k<k)
    q | inr p with TotalOrder.totality keyOrder min k
    q | inr p | inl (inl min<k) rewrite t = exFalso (TotalOrder.irreflexive keyOrder min<k)
    q | inr p | inl (inr k<min) rewrite t = exFalso (TotalOrder.irreflexive keyOrder k<min)
    q | inr p | inr x = refl
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k pr with TotalOrder.totality keyOrder min k
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = zero ; index<m = _ ; isHere = isHere } | inl (inl min<k) rewrite isHere = exFalso (TotalOrder.irreflexive keyOrder min<k)
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inl min<k) = lookupCertainReduced fst k record { index = index ; index<m = canRemoveSuccFrom<N index<m ; isHere = isHere }
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = zero ; index<m = _ ; isHere = isHere } | inl (inr k<min) rewrite isHere = exFalso (TotalOrder.irreflexive keyOrder k<min)
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) with TotalOrder.totality keyOrder a k
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) | inl (inl a<k) = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder k<min (TotalOrder.<Transitive keyOrder snd a<k)))
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) | inl (inr k<a) = exFalso h
  where
    f : Sg valueSet (λ v → lookupReduced fst k ≡ yes v)
    f = lookupCertainReduced fst k record { index = index ; index<m = canRemoveSuccFrom<N index<m ; isHere = isHere }
    g : lookupReduced fst k ≡ no
    g = lookupReducedWhenLess fst k k<a
    noIsNotYes : {a : _} → {A : Set a} → {b : A} → (no ≡ yes b) → False
    noIsNotYes {a} {A} {b} ()
    h : False
    h with f
    h | a , b rewrite g = noIsNotYes b
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) | inr refl = exFalso (TotalOrder.irreflexive keyOrder (TotalOrder.<Transitive keyOrder snd k<min))
lookupCertainReduced {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k pr | inr min=k = firstEntry , refl

lookupCertain : (m : Map) → (k : keySet) → (vecContains (keys m) k) → Sg valueSet (λ v → lookup m k ≡ yes v)
lookupCertain empty k record { index = index ; index<m = (le x ()) ; isHere = isHere }
lookupCertain (nonempty {min} m) k pr = lookupCertainReduced {min} m k pr
