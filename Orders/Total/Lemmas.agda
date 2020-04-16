{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae

open import Orders.Total.Definition

module Orders.Total.Lemmas {a b : _} {A : Set a} (order : TotalOrder A {b}) where

open TotalOrder order

equivMin : {x y : A} → (x < y) → min x y ≡ x
equivMin {x} {y} x<y with totality x y
equivMin {x} {y} x<y | inl (inl x₁) = refl
equivMin {x} {y} x<y | inl (inr y<x) = exFalso (irreflexive (<Transitive x<y y<x))
equivMin {x} {y} x<y | inr x=y rewrite x=y = refl

equivMin' : {x y : A} → (min x y ≡ x) → (x < y) || (x ≡ y)
equivMin' {x} {y} minEq with totality x y
equivMin' {x} {y} minEq | inl (inl x<y) = inl x<y
equivMin' {x} {y} minEq | inl (inr y<x) = exFalso (irreflexive (identityOfIndiscernablesLeft _<_ y<x minEq))
equivMin' {x} {y} minEq | inr x=y = inr x=y

minCommutes : (x y : A) → (min x y) ≡ (min y x)
minCommutes x y with totality x y
minCommutes x y | inl (inl x<y) with totality y x
minCommutes x y | inl (inl x<y) | inl (inl y<x) = exFalso (irreflexive (<Transitive y<x x<y))
minCommutes x y | inl (inl x<y) | inl (inr x<y') = refl
minCommutes x y | inl (inl x<y) | inr y=x = equalityCommutative y=x
minCommutes x y | inl (inr y<x) with totality y x
minCommutes x y | inl (inr y<x) | inl (inl y<x') = refl
minCommutes x y | inl (inr y<x) | inl (inr x<y) = exFalso (irreflexive (<Transitive y<x x<y))
minCommutes x y | inl (inr y<x) | inr y=x = refl
minCommutes x y | inr x=y with totality y x
minCommutes x y | inr x=y | inl (inl x₁) = x=y
minCommutes x y | inr x=y | inl (inr x₁) = refl
minCommutes x y | inr x=y | inr x₁ = x=y

minIdempotent : (x : A) → min x x ≡ x
minIdempotent x with totality x x
minIdempotent x | inl (inl x₁) = refl
minIdempotent x | inl (inr x₁) = refl
minIdempotent x | inr x₁ = refl

swapMin : {x y z : A} → (min x (min y z)) ≡ min y (min x z)
swapMin {x} {y} {z} with totality y z
swapMin {x} {y} {z} | inl (inl y<z) with totality x z
swapMin {x} {y} {z} | inl (inl y<z) | inl (inl x<z) = minCommutes x y
swapMin {x} {y} {z} | inl (inl y<z) | inl (inr z<x) with totality x y
swapMin {x} {y} {z} | inl (inl y<z) | inl (inr z<x) | inl (inl x<y) = exFalso (irreflexive (<Transitive y<z (<Transitive z<x x<y)))
swapMin {x} {y} {z} | inl (inl y<z) | inl (inr z<x) | inl (inr y<x) = equalityCommutative (equivMin y<z)
swapMin {x} {y} {z} | inl (inl y<z) | inl (inr z<x) | inr x=y rewrite x=y = equalityCommutative (equivMin y<z)
swapMin {x} {y} {z} | inl (inl y<z) | inr x=z = minCommutes x y
swapMin {x} {y} {z} | inl (inr z<y) with totality x z
swapMin {x} {y} {z} | inl (inr z<y) | inl (inl x<z) rewrite minCommutes y x = equalityCommutative (equivMin (<Transitive x<z z<y))
swapMin {x} {y} {z} | inl (inr z<y) | inl (inr z<x) with totality y z
swapMin {x} {y} {z} | inl (inr z<y) | inl (inr z<x) | inl (inl y<z) = exFalso (irreflexive (<Transitive z<y y<z))
swapMin {x} {y} {z} | inl (inr z<y) | inl (inr z<x) | inl (inr z<y') = refl
swapMin {x} {y} {z} | inl (inr z<y) | inl (inr z<x) | inr y=z = equalityCommutative y=z
swapMin {x} {y} {z} | inl (inr z<y) | inr x=z rewrite x=z | minCommutes y z = equalityCommutative (equivMin z<y)
swapMin {x} {y} {z} | inr y=z with totality x z
swapMin {x} {y} {z} | inr y=z | inl (inl x<z) = minCommutes x y
swapMin {x} {y} {z} | inr y=z | inl (inr z<x) rewrite y=z | minIdempotent z | minCommutes x z = equivMin z<x
swapMin {x} {y} {z} | inr y=z | inr x=z = minCommutes x y

minMin : {x y : A} → (min x (min x y)) ≡ min x y
minMin {x} {y} with totality x y
minMin {x} {y} | inl (inl x<y) = minIdempotent x
minMin {x} {y} | inl (inr y<x) with totality x y
minMin {x} {y} | inl (inr y<x) | inl (inl x<y) = exFalso (irreflexive (<Transitive y<x x<y))
minMin {x} {y} | inl (inr y<x) | inl (inr y<x') = refl
minMin {x} {y} | inl (inr y<x) | inr x=y = x=y
minMin {x} {y} | inr x=y = minIdempotent x

minFromBoth : {l x y : A} → (l < x) → (l < y) → (l < (min x y))
minFromBoth {a} {x = x} {y} prX prY with totality x y
minFromBoth {a} prX prY | inl (inl x<y) = prX
minFromBoth {a} prX prY | inl (inr y<x) = prY
minFromBoth {a} prX prY | inr x=y = prX
