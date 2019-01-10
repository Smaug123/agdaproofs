{-# OPTIONS --warning=error #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Naturals
open import Vectors

postulate
  extensionality : {a b : _} {S : Set a}{T : S → Set b} {f g : (x : S) → T x} → ((x : S) → f x ≡ g x) → f ≡ g

record Category {a b : _} : Set (lsuc (a ⊔ b)) where
  field
    objects : Set a
    arrows : objects → objects → Set b
    id : (x : objects) → arrows x x
    _∘_ : {x y z : objects} → arrows y z → arrows x y → arrows x z
    rightId : {x y : objects} → (f : arrows x y) → (id y) ∘ f ≡ f
    leftId : {x y : objects} → (f : arrows x y) → f ∘ (id x) ≡ f
    associative : {x y z w : objects} → (f : arrows z w) → (g : arrows y z) → (h : arrows x y) → (f ∘ (g ∘ h)) ≡ (f ∘ g) ∘ h

dual : {a b : _} → Category {a} {b} → Category {a} {b}
dual record { objects = objects ; arrows = arrows ; id = id ; _∘_ = _∘_ ; rightId = rightId ; leftId = leftId ; associative = associative } = record { objects = objects ; arrows = λ i j → arrows j i ; id = id ; _∘_ = λ {x y z} g f → f ∘ g ; rightId = λ {x y} f → leftId f ; leftId = λ {x y} f → rightId f ; associative = λ {x y z w} f g h → equalityCommutative (associative h g f) }

SET : {a : _} → Category {lsuc a} {a}
SET {a} = record { objects = Set a ; arrows = λ i j → (i → j) ; id = λ X x → x ; _∘_ = λ g f x → g (f x) ; rightId = λ f → refl ; leftId = λ f → refl ; associative = λ f g h → refl }

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
NatMonoid = record { objects = True ; arrows = λ _ _ → ℕ ; id = λ x → 0 ; _∘_ = λ f g → f +N g ; rightId = λ f → refl ; leftId = λ f → addZeroRight f ; associative = λ a b c → equalityCommutative (additionNIsAssociative a b c) }

DISCRETE : {a : _} (X : Set a) → Category {a} {a}
DISCRETE X = record { objects = X ; arrows = _≡_ ; id = λ x → refl ; _∘_ = λ f g → transitivity g f ; rightId = λ f → ≡Unique (transitivity f refl) f ; leftId = λ f → ≡Unique (transitivity refl f) f ; associative = λ f g h → ≡Unique (transitivity (transitivity h g) f) (transitivity h (transitivity g f)) }

record Functor {a b c d : _} (C : Category {a} {b}) (D : Category {c} {d}) : Set (a ⊔ b ⊔ c ⊔ d) where
  field
    onObj : Category.objects C → Category.objects D
    onArrow : {S T : Category.objects C} → Category.arrows C S T → Category.arrows D (onObj S) (onObj T)
    mapId : {T : Category.objects C} → onArrow (Category.id C T) ≡ Category.id D (onObj T)
    mapCompose : {X Y Z : Category.objects C} → (f : Category.arrows C X Y) (g : Category.arrows C Y Z) → onArrow (Category._∘_ C g f) ≡ Category._∘_ D (onArrow g) (onArrow f)

functorCompose : {a b c d e f : _} {B : Category {a} {b}} {C : Category {c} {d}} {D : Category {e} {f}} → (Functor C D) → (Functor B C) → (Functor B D)
functorCompose G F = record { onObj = λ x → Functor.onObj G (Functor.onObj F x) ; onArrow = λ f → Functor.onArrow G (Functor.onArrow F f) ; mapId = λ {T} → mapIdHelp G F T ; mapCompose = λ r s → mapComposeHelp G F r s }
  where
    mapIdHelp : {a b c d e f : _} {B : Category {a} {b}} {C : Category {c} {d}} {D : Category {e} {f}} → (G : Functor C D) → (F : Functor B C) → (T : Category.objects B) → Functor.onArrow G (Functor.onArrow F (Category.id B T)) ≡ Category.id D (Functor.onObj G (Functor.onObj F T))
    mapIdHelp {B = B} {C} {D} record { onObj = onObjG ; onArrow = onArrowG ; mapId = mapIdG ; mapCompose = mapComposeG } record { onObj = onObj ; onArrow = onArrow ; mapId = mapId ; mapCompose = mapCompose } T rewrite mapId {T} = mapIdG {onObj T}
    mapComposeHelp : {a b c d e f : _} {B : Category {a} {b}} {C : Category {c} {d}} {D : Category {e} {f}} → (G : Functor C D) → (F : Functor B C) → {S T U : Category.objects B} → (r : Category.arrows B S T) → (s : Category.arrows B T U) → (Functor.onArrow G (Functor.onArrow F (Category._∘_ B s r))) ≡ (Category._∘_ D (Functor.onArrow G (Functor.onArrow F s)) (Functor.onArrow G (Functor.onArrow F r)))
    mapComposeHelp {B = record { objects = objectsB ; arrows = arrowsB ; id = idB ; _∘_ = _∘B_ ; rightId = rightIdB ; leftId = leftIdB ; associative = associativeB }} {record { objects = objectsC ; arrows = arrowsC ; id = idC ; _∘_ = _∘C_ ; rightId = rightIdC ; leftId = leftIdC ; associative = associativeC }} {record { objects = objectsD ; arrows = arrowsD ; id = idD ; _∘_ = _∘D_ ; rightId = rightIdD ; leftId = leftIdD ; associative = associativeD }} record { onObj = onObjG ; onArrow = onArrowG ; mapId = mapIdG ; mapCompose = mapComposeG } record { onObj = onObjF ; onArrow = onArrowF ; mapId = mapIdF ; mapCompose = mapComposeF } {S} {T} {U} r s rewrite mapComposeF r s | mapComposeG (onArrowF r) (onArrowF s) = refl

idFunctor : {a b : _} (C : Category {a} {b}) → Functor C C
Functor.onObj (idFunctor C) = λ x → x
Functor.onArrow (idFunctor C) = λ f → f
Functor.mapId (idFunctor C) = refl
Functor.mapCompose (idFunctor C) = λ f g → refl

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
