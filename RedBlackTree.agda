{-# OPTIONS --warning=error --safe #-}

open import LogicalFormulae
open import Functions
open import Maybe

open import Naturals

module RedBlackTree where
  record BinaryTreeNode {a : _} (carrier : Set a) (order : TotalOrder carrier) (minValue : Maybe carrier) (maxValue : Maybe carrier) : Set a

  valueExtractor : {a : _} {carrier : Set a} {order : TotalOrder carrier} {minValue : Maybe carrier} {maxValue : Maybe carrier} → BinaryTreeNode {a} carrier order minValue maxValue → carrier

  record BinaryTreeNode {a} carrier order minValue maxValue where
    inductive
    field
      value : carrier
      min<=val : TotalOrder._<_ order min val
      leftChild : Maybe (Sg (BinaryTreeNode {a} carrier order minValue (yes value)) (λ i → TotalOrder._<_ order (valueExtractor {a} {carrier} {order} i) value))
      rightChild : Maybe (Sg (BinaryTreeNode {a} carrier order (yes value) maxValue) (λ i → TotalOrder._<_ order value (valueExtractor i)))

  valueExtractor t = BinaryTreeNode.value t

  lookup : {a : _} {carrier : Set a} {order : TotalOrder carrier} {minValue : Maybe carrier} {maxValue : Maybe carrier} → (t : BinaryTreeNode carrier order minValue maxValue) → (k : carrier) → Maybe carrier
  lookup {a} {carrier} {order} record { value = value ; leftChild = leftChild ; rightChild = rightChild } k with TotalOrder.totality order k value
  lookup {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = rightChild } k | inl (inl k<val) = no
  lookup {a} {carrier} {order} record { value = value ; leftChild = (yes (tree , _)) ; rightChild = rightChild } k | inl (inl k<val) = lookup tree k
  lookup {a} {carrier} {order} record { value = value ; leftChild = leftChild ; rightChild = no } k | inl (inr val<k) = no
  lookup {a} {carrier} {order} record { value = value ; leftChild = leftChild ; rightChild = (yes (tree , _)) } k | inl (inr val<k) = lookup tree k
  lookup {a} {carrier} {order} record { value = value ; leftChild = leftChild ; rightChild = rightChild } k | inr k=val = yes value

  addTree : {a : _} {carrier : Set a} {order : TotalOrder carrier} {minValue : Maybe carrier} {maxValue : Maybe carrier} → (t : BinaryTreeNode carrier order minValue maxValue) → (k : carrier) → BinaryTreeNode carrier order (yes (defaultValue k minValue)) (yes (defaultValue k maxValue))
  addTree {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = no } k with TotalOrder.totality order k value
  addTree {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = no } k | inl (inr val<k) = record { value = value ; leftChild = no ; rightChild = yes (record { value = k ; leftChild = no ; rightChild = no} , val<k)}
  addTree {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = no } k | inl (inl k<val) = record { value = value ; leftChild = yes (record { value = k ; leftChild = no ; rightChild = no} , k<val) ; rightChild = no }
  addTree {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = no } k | inr k=val = record { value = k ; leftChild = no ; rightChild = no }
  addTree {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = (yes x) } k with TotalOrder.totality order k value
  addTree {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = (yes child) } k | inl (inl k<val) = {!!}
  addTree {a} {carrier} {order} record { value = value ; leftChild = no ; rightChild = (yes child) } k | inl (inr val<k) = {!!}
  addTree {a} {carrier} {order} {minValue} {maxValue} record { value = value ; leftChild = no ; rightChild = (yes (child , pr)) } k | inr k=val = record { value = k ; leftChild = no ; rightChild = yes (typeCast child (applyEquality (λ i → BinaryTreeNode carrier order {!!} {!!}) {!!}) , {!!}) }
  addTree {a} {carrier} {order} record { value = value ; leftChild = (yes x) ; rightChild = rightChild } k = {!!}
