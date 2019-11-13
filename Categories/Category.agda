{-# OPTIONS --warning=error #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals.Naturals
open import Numbers.Naturals.Order
open import Vectors
open import Semirings.Definition
open import Categories.Definition

module Categories.Category where

postulate
  extensionality : {a b : _} {S : Set a} {T : S → Set b} {f g : (x : S) → T x} → ((x : S) → f x ≡ g x) → f ≡ g

≡Unique : {a : _} {X : Set a} → {a b : X} → (p1 p2 : a ≡ b) → (p1 ≡ p2)
≡Unique refl refl = refl

NatPreorder : Category {lzero} {lzero}
NatPreorder = record { objects = ℕ ; arrows = λ m n → m ≤N n ; id = λ x → inr refl ; _∘_ = λ f g → leqTransitive g f ; rightId = λ x<y → leqUnique (leqTransitive x<y (inr refl)) x<y ; leftId = λ x<y → leqUnique (leqTransitive (inr refl) x<y) x<y ; associative = λ z<=w y<=z x<=y → leqUnique (leqTransitive (leqTransitive x<=y y<=z) z<=w) (leqTransitive x<=y (leqTransitive y<=z z<=w)) }
  where
    leqTransitive : {a b c : ℕ} → (a ≤N b) → (b ≤N c) → (a ≤N c)
    leqTransitive (inl a<b) (inl b<c) = inl (orderIsTransitive a<b b<c)
    leqTransitive (inl a<b) (inr b=c) rewrite b=c = inl a<b
    leqTransitive (inr a=b) (inl b<c) rewrite a=b = inl b<c
    leqTransitive (inr a=b) (inr b=c) rewrite a=b | b=c = inr refl

    <Nunique : {a b : ℕ} → (p1 p2 : a <N b) → p1 ≡ p2
    <Nunique {a} {b} (le a-b pr1) (le a-b2 pr2) = go a-b pr1 a-b2 pr2 p'
      where
        p : a-b2 +N a ≡ a-b +N a
        p rewrite equalityCommutative pr1 = succInjective pr2
        p' : a-b2 ≡ a-b
        p' = canSubtractFromEqualityRight p
        go : (a-b : ℕ) (pr1 : succ (a-b +N a) ≡ b) (a-b2 : ℕ) (pr2 : succ (a-b2 +N a) ≡ b) (p : a-b2 ≡ a-b) → (le a-b pr1) ≡ (le a-b2 pr2)
        go a-b pr1 a-b2 pr2 eq rewrite eq = applyEquality (λ i → le a-b i) (≡Unique pr1 pr2)

    leqUnique : {a b : ℕ} → (p1 : a ≤N b) → (p2 : a ≤N b) → p1 ≡ p2
    leqUnique (inl a<b) (inl a<b2) = applyEquality inl (<Nunique a<b a<b2)
    leqUnique (inl a<b) (inr a=b) rewrite a=b = exFalso (lessIrreflexive a<b)
    leqUnique (inr a=b) (inl a<b) rewrite a=b = exFalso (lessIrreflexive a<b)
    leqUnique (inr a=b1) (inr a=b2) rewrite a=b1 | a=b2 = refl

NatMonoid : Category {lzero} {lzero}
NatMonoid = record { objects = True ; arrows = λ _ _ → ℕ ; id = λ x → 0 ; _∘_ = λ f g → f +N g ; rightId = λ f → refl ; leftId = λ f → Semiring.sumZeroRight ℕSemiring f ; associative = λ a b c → Semiring.+Associative ℕSemiring a b c }

typeCastCat : {a b c d : _} {C : Category {a} {b}} {D : Category {c} {d}} (F : Functor C D) (G : Functor C D) (S T : Category.objects C) (pr : Functor.onObj F ≡ Functor.onObj G) → Category.arrows D (Functor.onObj G S) (Functor.onObj G T) ≡ Category.arrows D (Functor.onObj F S) (Functor.onObj F T)
typeCastCat F G S T pr rewrite pr = refl

equalityFunctionsEqual : {a b : _} {A : Set a} {B : Set b} (f : A → (B ≡ B)) → (g : A → (B ≡ B)) → (f ≡ g)
equalityFunctionsEqual f g = extensionality λ x → ≡Unique (f x) (g x)

equalityFunctionsEqual' : {a b : _} {A : Set a} {B : Set b} (f : A → (B ≡ B)) → (g : A → (B ≡ B)) → (f ≡ g)
equalityFunctionsEqual' f g = extensionality λ x → ≡Unique (f x) (g x)

functorsEqual' : {a b c d : _} {C : Category {a} {b}} {D : Category {c} {d}} (F : Functor C D) (G : Functor C D) (objEq : (Functor.onObj F) ≡ Functor.onObj G) (arrEq : ∀ {S T : Category.objects C} → {f : Category.arrows C S T} → (Functor.onArrow F {S} {T} f ≡ (typeCast (Functor.onArrow G {S} {T} f) (typeCastCat F G S T objEq)))) → F ≡ G
functorsEqual' record { onObj = onObjF ; onArrow = onArrowF ; mapId = mapIdF ; mapCompose = mapComposeF } record { onObj = onObjG ; onArrow = onArrowG ; mapId = mapIdG ; mapCompose = mapComposeG } prObj prArr rewrite prObj = {!!}

VEC : {a : _} → ℕ → Functor (SET {a}) (SET {a})
VEC {a} n = record { onObj = λ X → Vec X n ; onArrow = λ f → λ v → vecMap f v ; mapId = extensionality mapId' ; mapCompose = λ f g → extensionality λ vec → help f g vec }
  where
    vecMapLemma : {a : _} {T : Set a} {n : ℕ} (v : Vec T n) → vecMap (Category.id SET T) v ≡ v
    vecMapLemma {a} v with inspect (SET {a})
    vecMapLemma {a} v | y with≡ SetCopy = vecMapIdFact (λ i → refl) v
    mapId' : {a : _} {T : Set a} {n : ℕ} → (v : Vec T n) → vecMap (Category.id SET T) v ≡ Category.id SET (Vec T n) v
    mapId' v rewrite vecMapLemma v = refl
    help : ∀ {a n} {X Y Z : Category.objects (SET {a})} (f : X → Y) (g : Y → Z) (vec : Vec X n) → vecMap (λ x → g (f x)) vec ≡ vecMap g (vecMap f vec)
    help f g vec = equalityCommutative (vecMapCompositionFact (λ x → refl) vec)

CATEGORY : {a b : _} → Category {lsuc b ⊔ lsuc a} {b ⊔ a}
CATEGORY {a} {b} = record { objects = Category {a} {b} ; arrows = λ C D → Functor C D ; _∘_ = λ F G → functorCompose F G ; id = λ C → idFunctor C ; rightId = λ F → {!!} ; leftId = λ F → {!!} ; associative = {!!} }
  where
    rightIdFact : {a b c d : _} → {C : Category {a} {b}} {D : Category {c} {d}} (F : Functor C D) → functorCompose (idFunctor D) F ≡ F
    rightIdFact {C = C} {D} F = {!!}
