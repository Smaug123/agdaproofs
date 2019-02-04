{-# OPTIONS --safe --warning=error #-}

open import LogicalFormulae
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Numbers.Naturals
open import Lists
open import Vectors

module Experiments where
  record One : Set where

  ListF : (A : Set) (T : Set) → Set
  ListF A T = One || A && T

  Choose : {I J : Set} -> (I -> Set) -> (J -> Set) -> (I || J) -> Set
  Choose X Y (inl i) = X i
  Choose X Y (inr j) = Y j

  data Poly (X : Set) : Set where
    var' : X -> Poly X
    konst' : Bool -> Poly X
    _+'_ _*'_ : Poly X -> Poly X -> Poly X

  Eval : {X : Set} -> (X -> Set) -> Poly X -> Set
  Eval elems (var' x) = elems x
  Eval elems (konst' BoolTrue) = One
  Eval elems (konst' BoolFalse) = False'
  Eval elems (poly +' poly1) = Eval elems poly || Eval elems poly1
  Eval elems (poly *' poly1) = Eval elems poly && Eval elems poly1

  data MU {elements nodes : Set} (nodeStructure : nodes → Poly (elements || nodes)) (elems : elements → Set) (topNode : nodes) : Set where
    <_> : Eval (Choose elems (MU nodeStructure elems)) (nodeStructure topNode) → MU nodeStructure elems topNode

  polyMap : {X Y : Set} → (f : X → Y) → Poly X → Poly Y
  polyMap f (var' x) = var' (f x)
  polyMap f (konst' x) = konst' x
  polyMap f (p +' q) = polyMap f p +' polyMap f q
  polyMap f (p *' q) = polyMap f p *' polyMap f q

-- Naturals
  natF : Poly One
  natF = konst' BoolTrue +' var' (record {})

  natF' : Poly (False || One)
  natF' = polyMap (λ _ → inr (record {})) natF

  nats : Set
  nats = MU {False} {One} (λ _ → natF') (λ ()) (record {})

  f : nats → ℕ
  f < inl record {} > = 0
  f < inr x > = succ (f x)

  g : ℕ → nats
  g zero = < inl (record {}) >
  g (succ n) = < inr (g n) >

  fgId : {n : ℕ} → f (g n) ≡ n
  fgId {zero} = refl
  fgId {succ n} rewrite fgId {n} = refl

  gfId : {n : nats} → g (f n) ≡ n
  gfId {< inl record {} >} = refl
  gfId {< inr x >} rewrite gfId {x} = refl

-- Lists
  listF : Poly (One || One)
  listF = konst' BoolTrue +' (var' (inl (record {})) *' var' (inr record {}))

  lists : (A : Set) → Set
  lists A = MU {One} {One} (λ _ → listF) (λ _ → A) record {}

  h : {A : Set} → lists A → List A
  h {A} < inl record {} > = []
  h {A} < inr (fst ,, snd) > = fst :: h snd

  i : {A : Set} → List A → lists A
  i {A} [] = < inl record {} >
  i {A} (x :: l) = < inr (x ,, i l) >

  hiId : {A : Set} → (r : List A) → h (i r) ≡ r
  hiId [] = refl
  hiId (x :: r) rewrite hiId r = refl

  ihId : {A : Set} → (r : lists A) → i (h r) ≡ r
  ihId < inl record {} > = refl
  ihId < inr (fst ,, snd) > rewrite ihId snd = refl

-- Vectors
  vecF : ℕ → Poly (One || ℕ)
  vecF zero = konst' BoolTrue
  vecF (succ n) = var' (inl (record {})) *' var' (inr n)

  vecs : (A : Set) (n : ℕ) → Set
  vecs A n = MU vecF (λ _ → A) n

  j : {A : Set} → {n : ℕ} → vecs A n → Vec A n
  j {A} {zero} < record {} > = []
  j {A} {succ n} < fst ,, snd > = fst ,- j snd

  k : {A : Set} → {n : ℕ} → Vec A n → vecs A n
  k {A} {.0} [] = < record {} >
  k {A} {.(succ _)} (x ,- v) = < x ,, k v >

  jkId : {A : Set} {n : ℕ} → {v : Vec A n} → j (k v) ≡ v
  jkId {A} {zero} {[]} = refl
  jkId {A} {succ n} {x ,- v} rewrite jkId {v = v} = refl

  kjId : {A : Set} {n : ℕ} {v : vecs A n} → k (j v) ≡ v
  kjId {n = zero} {< record {} >} = refl
  kjId {n = succ n} {< fst ,, snd >} rewrite kjId {v = snd} = refl

-- Vectors where even-numbered places are pairs
  evenQ : ℕ → Bool
  evenQ 0 = BoolTrue
  evenQ (succ n) = not (evenQ n)

  data VecWeird {a : _} (A : Set a) : ℕ → Set a where
    empty : VecWeird A 0
    consEven : {n : ℕ} → VecWeird A n → (evenQ n ≡ BoolFalse) → (A && A) → (VecWeird A (succ n))
    consOdd : {n : ℕ} → VecWeird A n → (evenQ n ≡ BoolTrue) → A → (VecWeird A (succ n))

  example : VecWeird ℕ 4
  example = consEven {n = 3} (consOdd (consEven (consOdd empty refl 4) refl (3 ,, 3)) refl 2) refl (1 ,, 1)

  vecWeirdF : (ℕ && Bool) → Poly (One || (ℕ && Bool))
  vecWeirdF (zero ,, BoolTrue) = konst' BoolTrue
  vecWeirdF (zero ,, BoolFalse) = konst' BoolFalse
  vecWeirdF ((succ n) ,, BoolTrue) = (var' (inl (record {}))  *' var' (inl (record {}))) *' var' (inr (n ,, BoolFalse))
  vecWeirdF ((succ n) ,, BoolFalse) = var' (inl (record {})) *' var' (inr (n ,, BoolTrue))

  vecWeirds : (A : Set) (n : ℕ) → Set
  vecWeirds A n = MU vecWeirdF (λ _ → A) (n ,, evenQ n)

  vecWeirdsEq : {A : Set} {n : ℕ} → VecWeird A n → vecWeirds A n
  vecWeirdsEq empty = < record {} >
  vecWeirdsEq {n = .succ n} (consEven v pr (x ,, y)) with inspect (evenQ n)
  vecWeirdsEq {_} {.(succ _)} (consEven v s (x ,, y)) | BoolTrue with≡ p rewrite p = exFalso (q s)
    where
      q : (BoolTrue ≡ BoolFalse) → False
      q ()
  vecWeirdsEq {A} {succ n} (consEven v _ (x ,, y)) | BoolFalse with≡ p rewrite p = < (x ,, y) ,, typeCast (vecWeirdsEq v) (applyEquality (MU vecWeirdF (λ _ → A)) b) >
    where
      b : (n ,, evenQ n) ≡ (n ,, BoolFalse)
      b rewrite p = refl
  vecWeirdsEq {_} {succ n} (consOdd v pr x) with inspect (evenQ n)
  vecWeirdsEq {A} {succ n} (consOdd v pr x) | BoolTrue with≡ _ rewrite pr = < x ,, typeCast (vecWeirdsEq v) (applyEquality (MU vecWeirdF (λ _ → A)) b) >
    where
      b : (n ,, evenQ n) ≡ (n ,, BoolTrue)
      b rewrite pr = refl
  vecWeirdsEq {_} {succ n} (consOdd v pr x) | BoolFalse with≡ q rewrite q = exFalso (r pr)
    where
      r : (BoolFalse ≡ BoolTrue) → False
      r ()

  vecWeirdsEq' : {A : Set} {n : ℕ} → vecWeirds A n → VecWeird A n
  vecWeirdsEq' {n = zero} < x > = empty
  vecWeirdsEq' {n = succ n} < x > with inspect (evenQ n)
  vecWeirdsEq' {A} {succ n} < x > | BoolTrue with≡ p = ans
    where
      y : Eval (Choose (λ _ → A) (MU vecWeirdF (λ _ → A))) (vecWeirdF (succ n ,, BoolFalse))
      y = typeCast x (applyEquality (λ i → Eval (Choose (λ _ → A) (MU vecWeirdF (λ _ → A))) (vecWeirdF (succ n ,, not i))) p)
      ans : VecWeird A (succ n)
      ans with y
      ans | fst ,, snd = consOdd (vecWeirdsEq' insert) p fst
        where
          insert : vecWeirds A n
          insert = typeCast snd (applyEquality (λ i → MU vecWeirdF (λ _ → A) (n ,, i)) (equalityCommutative p))
  vecWeirdsEq' {A} {succ n} < x > | BoolFalse with≡ p = ans
    where
      y : Eval (Choose (λ _ → A) (MU vecWeirdF (λ _ → A))) (vecWeirdF (succ n ,, BoolTrue))
      y = typeCast x (applyEquality (λ i → Eval (Choose (λ _ → A) (MU vecWeirdF (λ _ → A))) (vecWeirdF (succ n ,, not i))) p)
      ans : VecWeird A (succ n)
      ans with y
      ans | fst ,, snd = consEven (vecWeirdsEq' insert) p fst
        where
          insert : vecWeirds A n
          insert = typeCast snd (applyEquality (λ i → MU vecWeirdF (λ _ → A) (n ,, i)) (equalityCommutative p))

  vecWeirdsEquiv : {A : Set} {n : ℕ} {v : vecWeirds A n} → vecWeirdsEq (vecWeirdsEq' v) ≡ v
  vecWeirdsEquiv {A} {zero} {< record {} >} = refl
  vecWeirdsEquiv {A} {succ n} {< x >} with inspect (evenQ n)
  vecWeirdsEquiv {A} {succ n} {< x >} | BoolTrue with≡ pr = {!!}
  vecWeirdsEquiv {A} {succ n} {< x >} | BoolFalse with≡ pr = {!!}

  vecWeirdsEquiv' : {A : Set} {n : ℕ} {v : VecWeird A n} → vecWeirdsEq' (vecWeirdsEq v) ≡ v
  vecWeirdsEquiv' {A} {zero} {empty} = refl
  vecWeirdsEquiv' {A} {succ n} {consEven v x pr} with inspect (evenQ n)
  vecWeirdsEquiv' {A} {succ n} {consEven v x pr} | BoolTrue with≡ pr' = exFalso (fa x)
    where
      fa : (evenQ n ≡ BoolFalse) → False
      fa a rewrite pr' = b a
        where
          b : BoolTrue ≡ BoolFalse → False
          b ()
  vecWeirdsEquiv' {A} {succ n} {consEven v pr (fst ,, snd)} | BoolFalse with≡ pr' with vecWeirdsEquiv' {A} {n} {v}
  ... | bl = {!!}
  vecWeirdsEquiv' {A} {succ n} {consOdd v x pr} = {!!}

-- Trees
  treeF : Poly (One || One)
  treeF = konst' BoolTrue +' (var' (inl (record {})) *' (var' (inr record {}) *' var' (inr record {})))

  trees : (A : Set) → Set
  trees A = MU (λ _ → treeF) (λ _ → A) record {}

  data Tree {a : _} (A : Set a) : Set a where
    emptyTree : Tree A
    branch : Tree A → Tree A → A → Tree A

  treeEq : {A : Set} → trees A → Tree A
  treeEq < inl x > = emptyTree
  treeEq < inr (x ,, (branch1 ,, branch2)) > = branch (treeEq branch1) (treeEq branch2) x

  treeEq' : {A : Set} → Tree A → trees A
  treeEq' emptyTree = < inl (record {}) >
  treeEq' (branch left right x) = < inr (x ,, (treeEq' left ,, treeEq' right)) >

  treeEqId : {A : Set} → {t : Tree A} → treeEq (treeEq' t) ≡ t
  treeEqId {t = emptyTree} = refl
  treeEqId {t = branch left right x} rewrite treeEqId {t = left} | treeEqId {t = right} = refl

  treeEqId' : {A : Set} → {t : trees A} → treeEq' (treeEq t) ≡ t
  treeEqId' {t = < inl record {} >} = refl
  treeEqId' {t = < inr (a ,, (left ,, right)) >} rewrite treeEqId' {t = left} | treeEqId' {t = right} = refl

-- Expressions

  data Expr : (A : Set) → Set where
    constant : (A : Set) → A → Expr A
    plus : (a b : Expr ℕ) → Expr ℕ
    negate : (a : Expr Bool) → Expr Bool

  data ExprType : Set where
    nat : ExprType
    bool : ExprType
    a : ExprType

  data NodeType : Set where
    const' : NodeType
    plus' : NodeType
    negate' : NodeType

  exprF : NodeType → Poly (ExprType || NodeType)
  exprF const' = var' (inl a)
  exprF plus' = var' (inr {!!}) *' var' (inr {!!})
  exprF negate' = var' (inr {!!})

  exprShapes : (A : Set) → ExprType → Set
  exprShapes A nat = A
  exprShapes _ bool = ℕ && ℕ
  exprShapes _ a = Bool

  exprs : (A : Set) → Set
  exprs A = MU {ExprType} {NodeType} exprF (exprShapes A) const'

  exprsEq : {A : Set} → Expr A → exprs A
  exprsEq (constant A x) = < {!!} >
  exprsEq (plus e1 e2) with exprsEq e1
  exprsEq (plus e1 e2) | a1 with exprsEq e2
  exprsEq (plus e1 e2) | < x > | < y > = < {!!} >
  exprsEq (negate e) with exprsEq e
  ... | < toNegate > = < not toNegate >

  exprsEq' : {A : Set} → exprs A → Expr A
  exprsEq' < x > = {!!}

  exprsEqId : {A : Set} {e : Expr A} → exprsEq' (exprsEq e) ≡ e
  exprsEqId {e = constant A x} = {!!}
  exprsEqId {e = plus x y} with exprsEq x
  exprsEqId {_} {plus x y} | < x1 > with exprsEq y
  exprsEqId {_} {plus x y} | < x1 > | < y1 > = {!!}
  exprsEqId {e = negate e} = {!!}

  exprsEqId' : {A : Set} {e : exprs A} → exprsEq (exprsEq' e) ≡ e
  exprsEqId' {e = e} = {!!}
