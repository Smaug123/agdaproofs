{-# OPTIONS --safe --warning=error --without-K #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Naturals
open import Sets.FinSet
open import Semirings.Definition
open import Orders
open import WellFoundedInduction

module Sets.CantorBijection.Order where

order : Rel (ℕ && ℕ)
order (a ,, b) (c ,, d) = ((a +N b) <N (c +N d)) || (((a +N b) ≡ (c +N d)) && (b <N d))

totalOrder : TotalOrder (ℕ && ℕ)
PartialOrder._<_ (TotalOrder.order totalOrder) = order
PartialOrder.irreflexive (TotalOrder.order totalOrder) {fst ,, snd} (inl x) = exFalso (TotalOrder.irreflexive ℕTotalOrder x)
PartialOrder.irreflexive (TotalOrder.order totalOrder) {fst ,, snd} (inr (_ ,, p)) = exFalso (TotalOrder.irreflexive ℕTotalOrder p)
PartialOrder.<Transitive (TotalOrder.order totalOrder) {x1 ,, x2} {y1 ,, y2} {z1 ,, z2} (inl pr1) (inl pr2) = inl (TotalOrder.<Transitive ℕTotalOrder pr1 pr2)
PartialOrder.<Transitive (TotalOrder.order totalOrder) {x1 ,, x2} {y1 ,, y2} {z1 ,, z2} (inl pr1) (inr (f1 ,, f2)) = inl (identityOfIndiscernablesRight _<N_ pr1 f1)
PartialOrder.<Transitive (TotalOrder.order totalOrder) {x1 ,, x2} {y1 ,, y2} {z1 ,, z2} (inr (f1 ,, f2)) (inl x) = inl (identityOfIndiscernablesLeft _<N_ x (equalityCommutative f1))
PartialOrder.<Transitive (TotalOrder.order totalOrder) {x1 ,, x2} {y1 ,, y2} {z1 ,, z2} (inr (f1 ,, f2)) (inr (fst ,, snd)) = inr (transitivity f1 fst ,, TotalOrder.<Transitive ℕTotalOrder f2 snd)
TotalOrder.totality totalOrder (a ,, b) (c ,, d) with TotalOrder.totality ℕTotalOrder (a +N b) (c +N d)
TotalOrder.totality totalOrder (a ,, b) (c ,, d) | inl (inl x) = inl (inl (inl x))
TotalOrder.totality totalOrder (a ,, b) (c ,, d) | inl (inr x) = inl (inr (inl x))
TotalOrder.totality totalOrder (a ,, b) (c ,, d) | inr eq with TotalOrder.totality ℕTotalOrder b d
TotalOrder.totality totalOrder (a ,, b) (c ,, d) | inr eq | inl (inl x) = inl (inl (inr (eq ,, x)))
TotalOrder.totality totalOrder (a ,, b) (c ,, d) | inr eq | inl (inr x) = inl (inr (inr (equalityCommutative eq ,, x)))
TotalOrder.totality totalOrder (a ,, b) (c ,, .b) | inr eq | inr refl rewrite canSubtractFromEqualityRight {a} {b} {c} eq = inr refl

leastElement : {y : ℕ && ℕ} → order y (0 ,, 0) → False
leastElement {zero ,, b} (inl ())
leastElement {zero ,, b} (inr ())
leastElement {succ a ,, b} (inl ())
leastElement {succ a ,, b} (inr ())

mustDescend : (a b t : ℕ) → order (a ,, b) (t ,, zero) → a +N b <N t
mustDescend a b zero ord = exFalso (leastElement ord)
mustDescend a b (succ t) (inl x) rewrite Semiring.sumZeroRight ℕSemiring t = x

orderWellfounded : WellFounded order
orderWellfounded (a ,, b) = access (go b a)
  where
    g0 : (c : ℕ) (y : ℕ && ℕ) → order y (c ,, 0) → Accessible order y
    -- We want to induct on the second entry of x here, so we decompose so as to put that first.
    g : (x : ℕ) → ((y : ℕ) → y <N x → (b : ℕ) (z : ℕ && ℕ) → order z (b ,, y) → Accessible order z) → (c : ℕ) (y : ℕ && ℕ) → order y (c ,, x) → Accessible order y

    g0 = rec <NWellfounded (λ z → (x : ℕ && ℕ) (x₁ : order x (z ,, zero)) → Accessible order x) f
      where
        p : (a b : ℕ) → a ≡ b → (a ,, zero) ≡ (b ,, zero)
        p a .a refl = refl

        f : (x : ℕ) (x₁ : (x₂ : ℕ) (x₃ : x₂ <N x) (x₄ : ℕ && ℕ) (x₅ : order x₄ (x₂ ,, zero)) → Accessible order x₄) (x₂ : ℕ && ℕ) (x₃ : order x₂ (x ,, zero)) → Accessible order x₂
        f zero pr y ord = exFalso (leastElement ord)
        f (succ m) pr (fst ,, snd) (inl pr2) = h snd fst pr2
          where
            go : (x : ℕ) (x₁ : (x₂ : ℕ) (x₃ : x₂ <N x) (x₄ : ℕ) (x₅ : x₄ +N x₂ <N succ (m +N zero)) → Accessible order (x₄ ,, x₂)) (x₂ : ℕ) (x₃ : x₂ +N x <N succ (m +N zero)) → Accessible order (x₂ ,, x)
            go bound pr2 toProve bounded with TotalOrder.totality ℕTotalOrder (toProve +N bound) (m +N 0)
            ... | inl (inl bl) = pr m (le 0 refl) (toProve ,, bound) (inl bl)
            ... | inl (inr bl) = exFalso (noIntegersBetweenXAndSuccX (m +N 0) bl bounded)
            go zero pr2 toProve _ | inr bl rewrite Semiring.sumZeroRight ℕSemiring m | Semiring.sumZeroRight ℕSemiring toProve = access λ i i<z → pr m (le 0 refl) i (inl (mustDescend (_&&_.fst i) (_&&_.snd i) (m +N zero) (identityOfIndiscernablesLeft order (identityOfIndiscernablesRight order i<z (p toProve (m +N 0) (transitivity bl (equalityCommutative (Semiring.sumZeroRight ℕSemiring m))))) refl)))
            go (succ bound) pr2 toProve _ | inr bl = access desc
              where
                desc : (i : ℕ && ℕ) → (order i (toProve ,, succ bound)) → Accessible order i
                desc (i1 ,, i2) (inl ord) = pr m (le zero refl) (i1 ,, i2) (inl (identityOfIndiscernablesRight _<N_ ord bl))
                desc (i1 ,, i2) (inr (ord1 ,, ord2)) = pr2 i2 ord2 i1 (le 0 (applyEquality succ (transitivity ord1 bl)))

            h : (a : ℕ) (b : ℕ) (pr2 : b +N a <N succ m +N 0) → Accessible order (b ,, a)
            h = rec <NWellfounded (λ z → (x2 : ℕ) (x1 : x2 +N z <N succ (m +N zero)) → Accessible order (x2 ,, z)) go

    g zero _ = g0
    g (succ x) pr zero (y1 ,, y2) (inl pr1) with TotalOrder.totality ℕTotalOrder (y1 +N y2) x
    g (succ x) pr zero (y1 ,, y2) (inl pr1) | inl (inl y1+y2<x) = pr x (le 0 refl) zero (y1 ,, y2) (inl y1+y2<x)
    g (succ x) pr zero (y1 ,, y2) (inl pr1) | inl (inr x<y1+y2) = exFalso (noIntegersBetweenXAndSuccX x x<y1+y2 pr1)
    g (succ x) pr zero (y1 ,, y2) (inl pr1) | inr y1+y2=x = access (λ y y<zs → pr x (le 0 refl) zero y (ans y y<zs))
      where
        ans : (y : ℕ && ℕ) → order y (y1 ,, y2) → (_&&_.fst y +N _&&_.snd y <N x) || ((_&&_.fst y +N _&&_.snd y ≡ x) && (_&&_.snd y <N x))
        ans (fst ,, snd) (inl x) rewrite y1+y2=x = inl x
        ans (zero ,, snd) (inr (a1 ,, a2)) rewrite y1+y2=x | a1 = exFalso (bad x y1 y2 y1+y2=x a2)
          where
            bad : (x y1 y2 : ℕ) → y1 +N y2 ≡ x → x <N y2 → False
            bad x zero y2 y1+y2=x x<y2 = TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesRight _<N_ x<y2 y1+y2=x)
            bad x (succ y1) y2 y1+y2=x x<y2 rewrite equalityCommutative y1+y2=x = TotalOrder.irreflexive ℕTotalOrder (TotalOrder.<Transitive ℕTotalOrder x<y2 (identityOfIndiscernablesRight _<N_ (addingIncreases y2 y1) (Semiring.commutative ℕSemiring y2 (succ y1))))
        ans (succ fst ,, snd) (inr (a1 ,, a2)) rewrite y1+y2=x = inr (a1 ,, le fst a1)
    g (succ x) pr zero (zero ,, y2) (inr (fst ,, snd)) = exFalso (TotalOrder.irreflexive ℕTotalOrder (identityOfIndiscernablesLeft _<N_ snd fst))
    g (succ x) pr zero (succ y1 ,, y2) (inr (fst ,, snd)) = pr y2 snd (succ (succ y1)) (succ y1 ,, y2) (inl (le 0 refl))
    g (succ x) pr (succ c) y (inl z) = pr x (le 0 refl) (succ (succ c)) y (inl (identityOfIndiscernablesRight _<N_ z (applyEquality succ (transitivity (Semiring.commutative ℕSemiring c (succ x)) (applyEquality succ (Semiring.commutative ℕSemiring x c))))))
    g (succ x) pr (succ c) y (inr (fst ,, snd)) with TotalOrder.totality ℕTotalOrder (_&&_.snd y) x
    ... | inl (inl bl) = pr x (le 0 refl) (succ (succ c)) y (inr (transitivity fst (applyEquality succ (transitivity (Semiring.commutative ℕSemiring c (succ x)) (applyEquality succ (Semiring.commutative ℕSemiring x c)))) ,, bl))
    ... | inl (inr bl) = exFalso (noIntegersBetweenXAndSuccX x bl snd)
    g (succ x) pr (succ c) (y1 ,, .x) (inr (fst ,, _)) | inr refl with canSubtractFromEqualityRight {y1} {x} {succ (succ c)} (transitivity fst (applyEquality succ (transitivity (Semiring.commutative ℕSemiring c (succ x)) (applyEquality succ (Semiring.commutative ℕSemiring x c)))))
    g (succ x) pr (succ c) (.(succ (succ c)) ,, .x) (inr (_ ,, _)) | inr refl | refl = pr x (le 0 refl) (succ (succ (succ c))) (succ (succ c) ,, x) (inl (le 0 refl))

    go : (a : ℕ) → (b : ℕ) → (y : ℕ && ℕ) → order y (b ,, a) → Accessible order y
    go = rec <NWellfounded (λ (a : ℕ) → (b : ℕ) → (y : ℕ && ℕ) → order y (b ,, a) → Accessible order y) g
