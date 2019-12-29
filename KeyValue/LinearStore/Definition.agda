{-# OPTIONS --warning=error --safe --without-K #-}

open import Orders.Total.Definition
open import LogicalFormulae
open import Maybe

module KeyValue.LinearStore.Definition {a b : _} (keySet : Set a) (valueSet : Set b) {c : _} (keyOrder : TotalOrder keySet {c}) where

open import KeyValue.KeyValue keySet valueSet
open import KeyValue.LinearStore.Implementation keySet valueSet keyOrder

LinearStore : KeyValue Map
KeyValue.tryFind LinearStore = lookup
KeyValue.add LinearStore = addMap
KeyValue.empty LinearStore = empty
KeyValue.count LinearStore = count
KeyValue.lookupAfterAdd LinearStore empty k v with TotalOrder.totality keyOrder k k
KeyValue.lookupAfterAdd LinearStore empty k v | inl (inl x) = exFalso (TotalOrder.irreflexive keyOrder x)
KeyValue.lookupAfterAdd LinearStore empty k v | inl (inr x) = exFalso (TotalOrder.irreflexive keyOrder x)
KeyValue.lookupAfterAdd LinearStore empty k v | inr x = refl
KeyValue.lookupAfterAdd LinearStore (nonempty x) k v = lookupReducedSucceedsAfterAdd k v x
KeyValue.lookupAfterAdd' LinearStore empty k1 v k2 with TotalOrder.totality keyOrder k1 k2
KeyValue.lookupAfterAdd' LinearStore empty k1 v k2 | inl (inl x) = inr refl
KeyValue.lookupAfterAdd' LinearStore empty k1 v k2 | inl (inr x) = inr refl
KeyValue.lookupAfterAdd' LinearStore empty k1 v k2 | inr x = inl x
KeyValue.lookupAfterAdd' LinearStore (nonempty x) k1 v k2 with TotalOrder.totality keyOrder k1 k2
KeyValue.lookupAfterAdd' LinearStore (nonempty map) k1 v k2 | inl (inl x) with inspect (lookupReduced map k2)
KeyValue.lookupAfterAdd' LinearStore (nonempty map) k1 v k2 | inl (inl x) | no with≡ pr rewrite pr = inr (lookupReducedFailsAfterUnrelatedAdd k1 v k2 (inl x) map pr)
KeyValue.lookupAfterAdd' LinearStore (nonempty map) k1 v k2 | inl (inl x) | (yes lookedUp) with≡ pr rewrite pr = inr (lookupReducedSucceedsAfterUnrelatedAdd k1 v k2 lookedUp (inl x) map pr)
KeyValue.lookupAfterAdd' LinearStore (nonempty map) k1 v k2 | inl (inr x) with inspect (lookupReduced map k2)
KeyValue.lookupAfterAdd' LinearStore (nonempty map) k1 v k2 | inl (inr x) | no with≡ pr rewrite pr = inr (lookupReducedFailsAfterUnrelatedAdd k1 v k2 (inr x) map pr)
KeyValue.lookupAfterAdd' LinearStore (nonempty map) k1 v k2 | inl (inr x) | yes lookedUp with≡ pr rewrite pr = inr (lookupReducedSucceedsAfterUnrelatedAdd k1 v k2 lookedUp (inr x) map pr)
KeyValue.lookupAfterAdd' LinearStore (nonempty map) k1 v k2 | inr x = inl x
KeyValue.countAfterAdd' LinearStore empty _ _ _ = refl
KeyValue.countAfterAdd' LinearStore (nonempty x) k v = countReducedBehavesWhenAddingNotPresent k v x
KeyValue.countAfterAdd LinearStore empty _ _ _ ()
KeyValue.countAfterAdd LinearStore (nonempty map) k v1 v2 = countReducedBehavesWhenAddingPresent k v1 v2 map
