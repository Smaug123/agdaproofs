{-# OPTIONS --warning=error --safe --without-K #-}

open import LogicalFormulae
open import Orders
open import Maybe
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Vectors

open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order

module KeyValue.LinearStore.Implementation where
  record ReducedMap {a b c : _} (keys : Set a) (values : Set b) (keyOrder : TotalOrder {_} {c} keys) (min : keys) : Set (a ⊔ b ⊔ c)
  record ReducedMap {a} {b} {c} keys values keyOrder min where
    inductive
    field
      firstEntry : values
      next : Maybe (Sg keys (λ nextKey → (ReducedMap keys values keyOrder nextKey) && (TotalOrder._<_ keyOrder min nextKey)))

  addReducedMap : {a b c : _} → {keys : Set a} → {values : Set b} → {keyOrder : TotalOrder {_} {c} keys} → {min : keys} → (k : keys) → (v : values) → (m : ReducedMap {a} {b} keys values keyOrder min) → ReducedMap keys values keyOrder (TotalOrder.min keyOrder min k)
  addReducedMap {keyOrder = keyOrder} {min} k v m with TotalOrder.totality keyOrder min k
  addReducedMap {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) = record { firstEntry = firstEntry ; next = yes (k , (record { firstEntry = v ; next = no} ,, min<k))}
  addReducedMap {keyOrder = keyOrder} {min} k v record { firstEntry = minVal ; next = yes (nextKey , (m ,, pr)) } | inl (inl min<k) = record { firstEntry = minVal ; next = yes ((TotalOrder.min keyOrder nextKey k) , (addReducedMap {keyOrder = keyOrder} {_} k v m ,, minFromBoth {order = keyOrder} pr min<k))}
  addReducedMap {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } | inl (inr k<min) = record { firstEntry = v ; next = yes (min , (record { firstEntry = firstEntry ; next = next } ,, k<min)) }
  addReducedMap {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } | inr min=k rewrite min=k = record { firstEntry = v ; next = next }

  lookupReduced : {a b c : _} → {keys : Set a} → {values : Set b} → {keyOrder : TotalOrder {_} {c} keys} → {min : keys} → (m : ReducedMap keys values keyOrder min) → (target : keys) → Maybe values
  lookupReduced {keyOrder = keyOrder} {min} m k with TotalOrder.totality keyOrder min k
  lookupReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = no } k | inl (inl min<k) = no
  lookupReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, _))) } k | inl (inl min<k) = lookupReduced {keyOrder = keyOrder} {newMin} m k
  lookupReduced {keyOrder = keyOrder} {min} m k | inl (inr k<min) = no
  lookupReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = next } k | inr min=k = yes firstEntry

  countReduced : {a b c : _} {keys : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keys} {min : keys} → (m : ReducedMap keys values keyOrder min) → ℕ
  countReduced record { firstEntry = firstEntry ; next = no } = 1
  countReduced record { firstEntry = firstEntry ; next = (yes (key , (m ,, pr))) } = succ (countReduced m)

  lookupReducedSucceedsAfterAdd : {a b c : _} → {keys : Set a} → {values : Set b} → {keyOrder : TotalOrder {_} {c} keys} → {min : keys} → (k : keys) → (v : values) → (m : ReducedMap keys values keyOrder min) → (lookupReduced (addReducedMap k v m) k ≡ yes v)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) with TotalOrder.totality keyOrder k k
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) | inl (inl k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) | inl (inr k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inl _) | inr p = refl
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inl (inr k<min) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) min<k k<min))
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } | inl (inl min<k) | inr min=k rewrite min=k = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) | inl (inl _) = lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} k v m
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) | inl (inr k<min) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) min<k k<min))
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = (yes (newMin , (m ,, pr))) } | inl (inl min<k) | inr min=k rewrite min=k = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inl (inr k<min) with TotalOrder.totality keyOrder k k
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inl (inr k<min) | inl (inl k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inl (inr k<min) | inl (inr k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inl (inr k<min) | inr p = refl
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inr min=k with TotalOrder.totality keyOrder k k
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inr min=k | inl (inl k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inr min=k | inl (inr k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inr min=k | inr p with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inr min=k | inr p | inl (inl min<k) rewrite min=k = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<k)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {min} k v m | inr min=k | inr p | inl (inr k<min) rewrite min=k = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<min)
  lookupReducedSucceedsAfterAdd {keyOrder = keyOrder} {.k} k v record { firstEntry = firstEntry ; next = next } | inr refl | inr p | inr s = refl

  lookupReducedSucceedsAfterUnrelatedAdd : {a b c : _} → {keys : Set a} → {values : Set b} → {keyOrder : TotalOrder {_} {c} keys} → {min : keys} → (unrelatedK : keys) → (unrelatedV : values) → (k : keys) → (v : values) → ((TotalOrder._<_ keyOrder unrelatedK k) || (TotalOrder._<_ keyOrder k unrelatedK)) → (m : ReducedMap keys values keyOrder min) → (lookupReduced m k ≡ yes v) → lookupReduced (addReducedMap unrelatedK unrelatedV m) k ≡ yes v
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m lookupReducedSucceeds with TotalOrder.totality keyOrder min k'
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m lookupReducedSucceeds | inl (inl min<k') with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr record { firstEntry = firstEntry ; next = no } () | inl (inl min<k') | inl (inl min<k)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedSucceeds | inl (inl min<k') | inl (inl min<k) = lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {a} k' v' k v pr fst lookupReducedSucceeds
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inl x) m lookupReducedSucceeds | inl (inl min<k') | inl (inr k<min) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) k<min (PartialOrder.transitive (TotalOrder.order keyOrder) min<k' x)))
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inr k<k') m () | inl (inl min<k') | inl (inr k<min)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {.min} k' v' min v (inl x) m lookupReducedSucceeds | inl (inl min<k') | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) x min<k'))
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {.min} k' v' min v (inr x) record { firstEntry = v2 ; next = no } p | inl (inl min<k') | inr refl = applyEquality yes (yesInjective p)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {.min} k' v' min v (inr x) record { firstEntry = .v ; next = (yes (a , b)) } refl | inl (inl min<k') | inr refl = applyEquality yes refl
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) with TotalOrder.totality keyOrder k' k
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) | inl (inl k'<k) with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) | inl (inl k'<k) | inl (inl min<k) = lookupReducedSucceeds
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m () | inl (inr k'<min) | inl (inl k'<k) | inl (inr k<min)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m lookupReducedSucceeds | inl (inr k'<min) | inl (inl k'<k) | inr refl = lookupReducedSucceeds
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inl x) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) x k<k'))
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inr x) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inr _) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') | inl (inl x) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) x (PartialOrder.transitive (TotalOrder.order keyOrder) k<k' k'<min)))
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inr _) m () | inl (inr k'<min) | inl (inr k<k') | inl (inr x)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inr _) m lookupReducedSucceeds | inl (inr k'<min) | inl (inr k<k') | inr x rewrite x = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) k<k' k'<min))
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inl x) m lookupReducedSucceeds | inl (inr k'<min) | inr k'=k rewrite k'=k = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v (inr x) m lookupReducedSucceeds | inl (inr k'<min) | inr k'=k rewrite k'=k = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k v pr m lookupReducedSucceeds | inr refl with TotalOrder.totality keyOrder min k
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {k'} k' v' k v (inl _) record { firstEntry = firstEntry ; next = no } () | inr refl | inl (inl min<k)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {k'} k' v' k v (inl _) record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedSucceeds | inr refl | inl (inl min<k) = lookupReducedSucceeds
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {k'} k' v' k v (inr x) m lookupReducedSucceeds | inr refl | inl (inl min<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) min<k x))
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {k'} k' v' k v (inl x) m () | inr refl | inl (inr k<min)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {k'} k' v' k v (inr x) m () | inr refl | inl (inr k<min)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {.min} .min v' min v (inl x) m lookupReducedSucceeds | inr refl | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedSucceedsAfterUnrelatedAdd {keyOrder = keyOrder} {.min} .min v' min v (inr x) m lookupReducedSucceeds | inr refl | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)

  lookupReducedFailsAfterUnrelatedAdd : {a b c : _} → {keys : Set a} → {values : Set b} → {keyOrder : TotalOrder {_} {c} keys} → {min : keys} → (unrelatedK : keys) → (unrelatedV : values) → (k : keys) → ((TotalOrder._<_ keyOrder unrelatedK k) || (TotalOrder._<_ keyOrder k unrelatedK)) → (m : ReducedMap keys values keyOrder min) → (lookupReduced m k ≡ no) → lookupReduced (addReducedMap unrelatedK unrelatedV m) k ≡ no
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr m lookupReducedFails with TotalOrder.totality keyOrder min k'
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr m lookupReducedFails | inl (inl min<k') with TotalOrder.totality keyOrder min k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) with TotalOrder.totality keyOrder k' k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inl (inl x) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inl (inr x) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .k v' k (inl x) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .k v' k (inr x) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inl min<k') | inl (inl min<k) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedFails | inl (inl min<k') | inl (inl min<k) = lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} k' v' k pr fst lookupReducedFails
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr m lookupReducedFails | inl (inl min<k') | inl (inr k<min) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {.min} k' v' min pr m () | inl (inl min<k') | inr refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr m lookupReducedFails | inl (inr k'<min) with TotalOrder.totality keyOrder min k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) with TotalOrder.totality keyOrder k' k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) with TotalOrder.totality keyOrder min k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inl x₁) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inl x₁) record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = lookupReducedFails
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inr x₁) record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inr x₁) record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inl _) = lookupReducedFails
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inl (inr x) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inl k'<k) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<k)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inl (inr k<k') = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .k v' k (inl x) record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .k v' k (inr x) record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr k'<min) | inl (inl min<k) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) with TotalOrder.totality keyOrder k' k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) with TotalOrder.totality keyOrder min k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) | inl (inl min<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) k<min min<k))
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) | inl (inr k<min') = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inl _) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<min)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k (inr x) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inl k'<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) k'<k x))
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inl (inr k<k') = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .k v' k (inl x) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .k v' k (inr x) m lookupReducedFails | inl (inr k'<min) | inl (inr k<min) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} k' v' k pr m () | inl (inr k'<min) | inr min=k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .min v' k pr m lookupReducedFails | inr refl with TotalOrder.totality keyOrder min k
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .min v' k pr record { firstEntry = firstEntry ; next = no } lookupReducedFails | inr refl | inl (inl min<k) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .min v' k pr record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedFails | inr refl | inl (inl min<k) = lookupReducedFails
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .min v' k pr m lookupReducedFails | inr refl | inl (inr k<min) = refl
  lookupReducedFailsAfterUnrelatedAdd {keyOrder = keyOrder} {min} .min v' k pr m () | inr refl | inr min=k

  countReducedBehavesWhenAddingNotPresent : {a b c : _} {keys : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keys} {min : keys} → (k : keys) → (v : values) → (m : ReducedMap keys values keyOrder min) → (lookupReduced {keyOrder = keyOrder} m k ≡ no) → countReduced (addReducedMap k v m) ≡ succ (countReduced m)
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v m lookupReducedFails with TotalOrder.totality keyOrder k min
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) with TotalOrder.totality keyOrder min k
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) | inl (inl min<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) min<k k<min))
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) | inl (inr _) = refl
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inl k<min) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<min)
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr min<k) with TotalOrder.totality keyOrder min k
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = no } lookupReducedFails | inl (inr min<k) | inl (inl _) = refl
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedFails | inl (inr min<k) | inl (inl _) = applyEquality succ (countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} k v (_&&_.fst b) lookupReducedFails)
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr min<k) | inl (inr k<min) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) min<k k<min))
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v record { firstEntry = firstEntry ; next = next } lookupReducedFails | inl (inr min<k) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<k)
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {min} k v m lookupReducedFails | inr refl with TotalOrder.totality keyOrder min min
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {k} k v m lookupReducedFails | inr refl | inl (inl min<min) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<min)
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {k} k v m lookupReducedFails | inr refl | inl (inr min<min) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<min)
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {k} k v record { firstEntry = firstEntry ; next = no } () | inr refl | inr p
  countReducedBehavesWhenAddingNotPresent {keyOrder = keyOrder} {k} k v record { firstEntry = firstEntry ; next = (yes x) } () | inr refl | inr p

  countReducedBehavesWhenAddingPresent : {a b c : _} {keys : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keys} {min : keys} → (k : keys) → (v v' : values) → (m : ReducedMap keys values keyOrder min) → (lookupReduced {keyOrder = keyOrder} m k ≡ yes v') → countReduced (addReducedMap k v m) ≡ countReduced m
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds with TotalOrder.totality keyOrder k min
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inl (inl k<min) with TotalOrder.totality keyOrder min k
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inl (inl k<min) | inl (inl min<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) k<min min<k))
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m () | inl (inl k<min) | inl (inr _)
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inl (inl k<min) | inr q = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (identityOfIndiscernablesLeft (TotalOrder._<_ keyOrder) k<min (equalityCommutative q)))
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inl (inr min<k) with TotalOrder.totality keyOrder min k
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = no } () | inl (inr min<k) | inl (inl _)
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } lookupReducedSucceeds | inl (inr min<k) | inl (inl _) = applyEquality succ (countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} k v v' fst lookupReducedSucceeds)
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m () | inl (inr min<k) | inl (inr k<min)
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inl (inr min<k) | inr q = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (identityOfIndiscernablesLeft (λ a b → TotalOrder._<_ keyOrder a b) min<k q))
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inr q with TotalOrder.totality keyOrder min min
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inr q | inl (inl x) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' m lookupReducedSucceeds | inr q | inl (inr x) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) x)
  countReducedBehavesWhenAddingPresent {keys = keys} {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = no } lookupReducedSucceeds | inr _ | inr p with TotalOrder.totality keyOrder min k
  countReducedBehavesWhenAddingPresent {keys = keys} {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = no } () | inr _ | inr p | inl (inl x)
  countReducedBehavesWhenAddingPresent {keys = keys} {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = no } () | inr _ | inr p | inl (inr x`)
  countReducedBehavesWhenAddingPresent {keys = keys} {keyOrder = keyOrder} {.k} k v v' record { firstEntry = firstEntry ; next = no } lookupReducedSucceeds | inr q | inr p | inr refl = refl
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedSucceeds | inr q | inr p with TotalOrder.totality keyOrder k k
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedSucceeds | inr q | inr p | inl (inl x) = exFalso (TotalOrder.irreflexive keyOrder x)
  countReducedBehavesWhenAddingPresent {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , b)) } lookupReducedSucceeds | inr q | inr p | inl (inr x) = exFalso (TotalOrder.irreflexive keyOrder x)
  countReducedBehavesWhenAddingPresent {keys = keys} {values = values} {keyOrder = keyOrder} {min} k v v' record { firstEntry = firstEntry ; next = (yes (a , (m ,, pr))) } q | inr q1 | inr p | inr x with TotalOrder.totality keyOrder min k
  countReducedBehavesWhenAddingPresent {keys = keys} {values} {keyOrder} {.k} k v v' record { firstEntry = firstEntry ; next = (yes (a , (m ,, pr))) } q | inr refl | inr p | inr x | inl (inl min<k) = exFalso (TotalOrder.irreflexive keyOrder min<k)
  countReducedBehavesWhenAddingPresent {keys = keys} {values} {keyOrder} {.k} k v v' record { firstEntry = firstEntry ; next = (yes (a , (m ,, pr))) } q | inr q1 | inr p | inr x | inr refl = refl

  data Map {a b c : _} (keys : Set a) (values : Set b) (keyOrder : TotalOrder {_} {c} keys) : Set (a ⊔ b ⊔ c) where
    empty : Map keys values keyOrder
    nonempty : {min : keys} → ReducedMap keys values keyOrder min → Map keys values keyOrder

  addMap : {a b c : _} → {keys : Set a} → {values : Set b} → {keyOrder : TotalOrder {_} {c} keys} → (m : Map keys values keyOrder) → (k : keys) → (v : values) → Map keys values keyOrder
  addMap empty k v = nonempty {min = k} record { firstEntry = v ; next = no }
  addMap {keys = keys} {values} {keyOrder} (nonempty x) k v = nonempty (addReducedMap {keys = keys} {values} {keyOrder} k v x)

  lookup : {a b c : _} → {keys : Set a} → {values : Set b} → {keyOrder : TotalOrder {_} {c} keys} → (m : Map keys values keyOrder) → (target : keys) → Maybe values
  lookup {keyOrder = keyOrder} empty t = no
  lookup {keyOrder = keyOrder} (nonempty x) t = lookupReduced x t

  count : {a b c : _} {keys : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keys} → (m : Map keys values keyOrder) → ℕ
  count {keyOrder = keyOrder} empty = 0
  count {keyOrder = keyOrder} (nonempty x) = countReduced x

  keysReduced : {a b c : _} {keyDom : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keyDom} {min : keyDom} → (m : ReducedMap keyDom values keyOrder min) → Vec keyDom (countReduced m)
  keysReduced {min = min} record { firstEntry = firstEntry ; next = no } = min ,- []
  keysReduced {min = min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } = min ,- (keysReduced fst)

  keys : {a b c : _} {keyDom : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keyDom} → (m : Map keyDom values keyOrder) → Vec keyDom (count m)
  keys empty = []
  keys (nonempty m) = keysReduced m

  lookupReducedWhenLess : {a b c : _} {keyDom : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keyDom} {min : keyDom} → (m : ReducedMap keyDom values keyOrder min) → (k : keyDom) → (TotalOrder._<_ keyOrder k min) → (lookupReduced m k ≡ no)
  lookupReducedWhenLess {keyOrder = keyOrder} {min} m k k<min with TotalOrder.totality keyOrder min k
  lookupReducedWhenLess {keyOrder = keyOrder} {min} m k k<min | inl (inl min<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) k<min min<k))
  lookupReducedWhenLess {keyOrder = keyOrder} {min} m k k<min | inl (inr _) = refl
  lookupReducedWhenLess {keyOrder = keyOrder} {min} m k k<min | inr min=k rewrite min=k = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<min)

  lookupCertainReduced : {a b c : _} {keyDom : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keyDom} {min : keyDom} → (m : ReducedMap keyDom values keyOrder min) → (k : keyDom) → (vecContains (keysReduced m) k) → Sg values (λ v → lookupReduced m k ≡ yes v)
  lookupCertainReduced {keyDom = keyDom} {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = no } k pr = firstEntry , q
    where
      t : min ≡ k
      t = vecSolelyContains k pr
      q : lookupReduced {keys = keyDom} {keyOrder = keyOrder} {min} (record { firstEntry = firstEntry ; next = no }) k ≡ yes firstEntry
      q with TotalOrder.totality keyOrder k k
      q | inl (inl k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
      q | inl (inr k<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<k)
      q | inr p with TotalOrder.totality keyOrder min k
      q | inr p | inl (inl min<k) rewrite t = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<k)
      q | inr p | inl (inr k<min) rewrite t = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<min)
      q | inr p | inr x = refl
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k pr with TotalOrder.totality keyOrder min k
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = zero ; index<m = _ ; isHere = isHere } | inl (inl min<k) rewrite isHere = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) min<k)
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inl min<k) = lookupCertainReduced {keyOrder = keyOrder} fst k record { index = index ; index<m = canRemoveSuccFrom<N index<m ; isHere = isHere }
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = zero ; index<m = _ ; isHere = isHere } | inl (inr k<min) rewrite isHere = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) k<min)
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) with TotalOrder.totality keyOrder a k
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) | inl (inl a<k) = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) k<min (PartialOrder.transitive (TotalOrder.order keyOrder) snd a<k)))
  lookupCertainReduced {values = values} {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) | inl (inr k<a) = exFalso h
    where
      f : Sg values (λ v → lookupReduced fst k ≡ yes v)
      f = lookupCertainReduced {keyOrder = keyOrder} fst k record { index = index ; index<m = canRemoveSuccFrom<N index<m ; isHere = isHere }
      g : lookupReduced fst k ≡ no
      g = lookupReducedWhenLess fst k k<a
      noIsNotYes : {a : _} → {A : Set a} → {b : A} → (no ≡ yes b) → False
      noIsNotYes {a} {A} {b} ()
      h : False
      h with f
      h | a , b rewrite g = noIsNotYes b
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k record { index = (succ index) ; index<m = index<m ; isHere = isHere } | inl (inr k<min) | inr refl = exFalso (PartialOrder.irreflexive (TotalOrder.order keyOrder) (PartialOrder.transitive (TotalOrder.order keyOrder) snd k<min))
  lookupCertainReduced {keyOrder = keyOrder} {min} record { firstEntry = firstEntry ; next = (yes (a , (fst ,, snd))) } k pr | inr min=k = firstEntry , refl

  lookupCertain : {a b c : _} {keyDom : Set a} {values : Set b} {keyOrder : TotalOrder {_} {c} keyDom} → (m : Map keyDom values keyOrder) → (k : keyDom) → (vecContains (keys m) k) → Sg values (λ v → lookup m k ≡ yes v)
  lookupCertain {keyOrder = keyOrder} empty k record { index = index ; index<m = (le x ()) ; isHere = isHere }
  lookupCertain {keyOrder = keyOrder} (nonempty {min} m) k pr = lookupCertainReduced {keyOrder = keyOrder} {min} m k pr
