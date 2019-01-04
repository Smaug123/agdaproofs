{-# OPTIONS --safe --warning=error #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions

module Orders where

  record PartialOrder {a b : _} (carrier : Set a) : Set (a ⊔ lsuc b) where
    field
      _<_ : Rel {a} {b} carrier
      irreflexive : {x : carrier} → (x < x) → False
      transitive : {a b c : carrier} → (a < b) → (b < c) → (a < c)

  record TotalOrder {a b : _} (carrier : Set a) : Set (a ⊔ lsuc b) where
    field
      order : PartialOrder {a} {b} carrier
    _<_ : Rel carrier
    _<_ = PartialOrder._<_ order
    field
      totality : (a b : carrier) → ((a < b) || (b < a)) || (a ≡ b)
    min : carrier → carrier → carrier
    min a b with totality a b
    min a b | inl (inl a<b) = a
    min a b | inl (inr b<a) = b
    min a b | inr a=b = a
    max : carrier → carrier → carrier
    max a b with totality a b
    max a b | inl (inl a<b) = b
    max a b | inl (inr b<a) = a
    max a b | inr a=b = b

  equivMin : {a b : _} {A : Set a} → (order : TotalOrder {a} {b} A) → {x y : A} → (TotalOrder._<_ order x y) → TotalOrder.min order x y ≡ x
  equivMin order {x} {y} x<y with TotalOrder.totality order x y
  equivMin order {x} {y} x<y | inl (inl x₁) = refl
  equivMin order {x} {y} x<y | inl (inr y<x) = exFalso (PartialOrder.irreflexive (TotalOrder.order order) (PartialOrder.transitive (TotalOrder.order order) x<y y<x))
  equivMin order {x} {y} x<y | inr x=y rewrite x=y = refl

  equivMin' : {a b : _} {A : Set a} → (order : TotalOrder {a} {b} A) → {x y : A} → (TotalOrder.min order x y ≡ x) → (TotalOrder._<_ order x y) || (x ≡ y)
  equivMin' order {x} {y} minEq with TotalOrder.totality order x y
  equivMin' order {x} {y} minEq | inl (inl x<y) = inl x<y
  equivMin' order {x} {y} minEq | inl (inr y<x) = exFalso (PartialOrder.irreflexive (TotalOrder.order order) (identityOfIndiscernablesLeft y _ x (TotalOrder._<_ order) y<x minEq))
  equivMin' order {x} {y} minEq | inr x=y = inr x=y

  minCommutes : {a b : _} {A : Set a} → (order : TotalOrder {a} {b} A) → (x y : A) → (TotalOrder.min order x y) ≡ (TotalOrder.min order y x)
  minCommutes order x y with TotalOrder.totality order x y
  minCommutes order x y | inl (inl x<y) with TotalOrder.totality order y x
  minCommutes order x y | inl (inl x<y) | inl (inl y<x) = exFalso (PartialOrder.irreflexive (TotalOrder.order order) (PartialOrder.transitive (TotalOrder.order order) y<x x<y))
  minCommutes order x y | inl (inl x<y) | inl (inr x<y') = refl
  minCommutes order x y | inl (inl x<y) | inr y=x = equalityCommutative y=x
  minCommutes order x y | inl (inr y<x) with TotalOrder.totality order y x
  minCommutes order x y | inl (inr y<x) | inl (inl y<x') = refl
  minCommutes order x y | inl (inr y<x) | inl (inr x<y) = exFalso (PartialOrder.irreflexive (TotalOrder.order order) (PartialOrder.transitive (TotalOrder.order order) y<x x<y))
  minCommutes order x y | inl (inr y<x) | inr y=x = refl
  minCommutes order x y | inr x=y with TotalOrder.totality order y x
  minCommutes order x y | inr x=y | inl (inl x₁) = x=y
  minCommutes order x y | inr x=y | inl (inr x₁) = refl
  minCommutes order x y | inr x=y | inr x₁ = x=y

  minIdempotent : {a b : _} {A : Set a} → (order : TotalOrder {a} {b} A) → (x : A) → TotalOrder.min order x x ≡ x
  minIdempotent order x with TotalOrder.totality order x x
  minIdempotent order x | inl (inl x₁) = refl
  minIdempotent order x | inl (inr x₁) = refl
  minIdempotent order x | inr x₁ = refl

  swapMin : {a b : _} {A : Set a} {order : TotalOrder {a} {b} A} {x y z : A} → (TotalOrder.min order x (TotalOrder.min order y z)) ≡ TotalOrder.min order y (TotalOrder.min order x z)
  swapMin {order = order} {x} {y} {z} with TotalOrder.totality order y z
  swapMin {order = order} {x} {y} {z} | inl (inl y<z) with TotalOrder.totality order x z
  swapMin {order = order} {x} {y} {z} | inl (inl y<z) | inl (inl x<z) = minCommutes order x y
  swapMin {order = order} {x} {y} {z} | inl (inl y<z) | inl (inr z<x) with TotalOrder.totality order x y
  swapMin {order = order} {x} {y} {z} | inl (inl y<z) | inl (inr z<x) | inl (inl x<y) = exFalso (PartialOrder.irreflexive (TotalOrder.order order) (PartialOrder.transitive (TotalOrder.order order) y<z (PartialOrder.transitive (TotalOrder.order order) z<x x<y)))
  swapMin {order = order} {x} {y} {z} | inl (inl y<z) | inl (inr z<x) | inl (inr y<x) = equalityCommutative (equivMin order y<z)
  swapMin {order = order} {x} {y} {z} | inl (inl y<z) | inl (inr z<x) | inr x=y rewrite x=y = equalityCommutative (equivMin order y<z)
  swapMin {order = order} {x} {y} {z} | inl (inl y<z) | inr x=z = minCommutes order x y
  swapMin {order = order} {x} {y} {z} | inl (inr z<y) with TotalOrder.totality order x z
  swapMin {order = order} {x} {y} {z} | inl (inr z<y) | inl (inl x<z) rewrite minCommutes order y x = equalityCommutative (equivMin order (PartialOrder.transitive (TotalOrder.order order) x<z z<y))
  swapMin {order = order} {x} {y} {z} | inl (inr z<y) | inl (inr z<x) with TotalOrder.totality order y z
  swapMin {order = order} {x} {y} {z} | inl (inr z<y) | inl (inr z<x) | inl (inl y<z) = exFalso (PartialOrder.irreflexive (TotalOrder.order order) (PartialOrder.transitive (TotalOrder.order order) z<y y<z))
  swapMin {order = order} {x} {y} {z} | inl (inr z<y) | inl (inr z<x) | inl (inr z<y') = refl
  swapMin {order = order} {x} {y} {z} | inl (inr z<y) | inl (inr z<x) | inr y=z = equalityCommutative y=z
  swapMin {order = order} {x} {y} {z} | inl (inr z<y) | inr x=z rewrite x=z | minCommutes order y z = equalityCommutative (equivMin order z<y)
  swapMin {order = order} {x} {y} {z} | inr y=z with TotalOrder.totality order x z
  swapMin {order = order} {x} {y} {z} | inr y=z | inl (inl x<z) = minCommutes order x y
  swapMin {order = order} {x} {y} {z} | inr y=z | inl (inr z<x) rewrite y=z | minIdempotent order z | minCommutes order x z = equivMin order z<x
  swapMin {order = order} {x} {y} {z} | inr y=z | inr x=z = minCommutes order x y

  minMin : {a b : _} {A : Set a} → (order : TotalOrder {a} {b} A) → {x y : A} → (TotalOrder.min order x (TotalOrder.min order x y)) ≡ TotalOrder.min order x y
  minMin order {x} {y} with TotalOrder.totality order x y
  minMin order {x} {y} | inl (inl x<y) = minIdempotent order x
  minMin order {x} {y} | inl (inr y<x) with TotalOrder.totality order x y
  minMin order {x} {y} | inl (inr y<x) | inl (inl x<y) = exFalso (PartialOrder.irreflexive (TotalOrder.order order) (PartialOrder.transitive (TotalOrder.order order) y<x x<y))
  minMin order {x} {y} | inl (inr y<x) | inl (inr y<x') = refl
  minMin order {x} {y} | inl (inr y<x) | inr x=y = x=y
  minMin order {x} {y} | inr x=y = minIdempotent order x

  minFromBoth : {a b : _} {A : Set a} → {order : TotalOrder {a} {b} A} → {min x y : A} → (TotalOrder._<_ order min x) → (TotalOrder._<_ order min y) → (TotalOrder._<_ order min (TotalOrder.min order x y))
  minFromBoth {a} {order = order} {x = x} {y} prX prY with TotalOrder.totality order x y
  minFromBoth {a} prX prY | inl (inl x<y) = prX
  minFromBoth {a} prX prY | inl (inr y<x) = prY
  minFromBoth {a} prX prY | inr x=y = prX
