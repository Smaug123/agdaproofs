{-# OPTIONS --warning=error --safe --without-K #-}

open import KeyValue.LinearStore.Implementation
open import KeyValue.KeyValue
open import Orders
open import LogicalFormulae
open import Maybe

module KeyValue.LinearStore.Definition where
  LinearStore : {a b c : _} (keys : Set a) (values : Set b) (keyOrder : TotalOrder {_} {c} keys) → KeyValue keys values (Map keys values keyOrder)
  KeyValue.tryFind (LinearStore keys values keyOrder) = lookup {keys = keys} {values} {keyOrder}
  KeyValue.add (LinearStore keys values keyOrder) = addMap
  KeyValue.empty (LinearStore keys values keyOrder) = empty
  KeyValue.count (LinearStore keys values keyOrder) = count {keys = keys} {values} {keyOrder}
  KeyValue.lookupAfterAdd (LinearStore keys values keyOrder) empty k v with TotalOrder.totality keyOrder k k
  KeyValue.lookupAfterAdd (LinearStore keys values keyOrder) empty k v | inl (inl x) = exFalso (TotalOrder.irreflexive keyOrder x)
  KeyValue.lookupAfterAdd (LinearStore keys values keyOrder) empty k v | inl (inr x) = exFalso (TotalOrder.irreflexive keyOrder x)
  KeyValue.lookupAfterAdd (LinearStore keys values keyOrder) empty k v | inr x = refl
  KeyValue.lookupAfterAdd (LinearStore keys values keyOrder) (nonempty x) k v = lookupReducedSucceedsAfterAdd k v x
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) empty k1 v k2 with TotalOrder.totality keyOrder k1 k2
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) empty k1 v k2 | inl (inl x) = inr refl
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) empty k1 v k2 | inl (inr x) = inr refl
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) empty k1 v k2 | inr x = inl x
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty x) k1 v k2 with TotalOrder.totality keyOrder k1 k2
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty map) k1 v k2 | inl (inl x) with inspect (lookupReduced map k2)
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty map) k1 v k2 | inl (inl x) | no with≡ pr rewrite pr = inr (lookupReducedFailsAfterUnrelatedAdd k1 v k2 (inl x) map pr)
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty map) k1 v k2 | inl (inl x) | (yes lookedUp) with≡ pr rewrite pr = inr (lookupReducedSucceedsAfterUnrelatedAdd k1 v k2 lookedUp (inl x) map pr)
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty map) k1 v k2 | inl (inr x) with inspect (lookupReduced map k2)
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty map) k1 v k2 | inl (inr x) | no with≡ pr rewrite pr = inr (lookupReducedFailsAfterUnrelatedAdd k1 v k2 (inr x) map pr)
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty map) k1 v k2 | inl (inr x) | yes lookedUp with≡ pr rewrite pr = inr (lookupReducedSucceedsAfterUnrelatedAdd k1 v k2 lookedUp (inr x) map pr)
  KeyValue.lookupAfterAdd' (LinearStore keys values keyOrder) (nonempty map) k1 v k2 | inr x = inl x
  KeyValue.countAfterAdd' (LinearStore keys values keyOrder) empty _ _ _ = refl
  KeyValue.countAfterAdd' (LinearStore keys values keyOrder) (nonempty x) k v = countReducedBehavesWhenAddingNotPresent k v x
  KeyValue.countAfterAdd (LinearStore keys values keyOrder) empty _ _ _ ()
  KeyValue.countAfterAdd (LinearStore keys values keyOrder) (nonempty map) k v1 v2 = countReducedBehavesWhenAddingPresent k v1 v2 map
