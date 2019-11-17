{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions
open import Numbers.Naturals.Semiring -- for length
open import Numbers.Naturals.Order
open import Semirings.Definition

module Lists.Lists where
  data List {a} (A : Set a) : Set a where
    [] : List A
    _::_ : (x : A) (xs : List A) → List A
  infixr 10 _::_

  [_] : {a : _} → {A : Set a} → (a : A) → List A
  [ a ] = a :: []

  _++_ : {a : _} → {A : Set a} → List A → List A → List A
  [] ++ m = m
  (x :: l) ++ m = x :: (l ++ m)

  appendEmptyList : {a : _} → {A : Set a} → (l : List A) → (l ++ [] ≡ l)
  appendEmptyList [] = refl
  appendEmptyList (x :: l) = applyEquality (_::_ x) (appendEmptyList l)

  concatAssoc : {a : _} → {A : Set a} → (x : List A) → (y : List A) → (z : List A) → ((x ++ y) ++ z) ≡ x ++ (y ++ z)
  concatAssoc [] m n = refl
  concatAssoc (x :: l) m n = applyEquality (_::_ x) (concatAssoc l m n)

  canMovePrepend : {a : _} → {A : Set a} → (l : A) → {m n : ℕ} → (x : List A) (y : List A) → ((l :: x) ++ y ≡ l :: (x ++ y))
  canMovePrepend l [] n = refl
  canMovePrepend l (x :: m) n = refl

  rev : {a : _} → {A : Set a} → List A → List A
  rev [] = []
  rev (x :: l) = (rev l) ++ [ x ]

  revIsHom : {a : _} → {A : Set a} → (l1 : List A) → (l2 : List A) → (rev (l1 ++ l2) ≡ (rev l2) ++ (rev l1))
  revIsHom l1 [] = applyEquality rev (appendEmptyList l1)
  revIsHom [] (x :: l2) with (rev l2 ++ [ x ])
  ... | r = equalityCommutative (appendEmptyList r)
  revIsHom (w :: l1) (x :: l2) = transitivity t (equalityCommutative s)
    where
      s : ((rev l2 ++ [ x ]) ++ (rev l1 ++ [ w ])) ≡ (((rev l2 ++ [ x ]) ++ rev l1) ++ [ w ])
      s = equalityCommutative (concatAssoc (rev l2 ++ (x :: [])) (rev l1) ([ w ]))
      t' : rev (l1 ++ (x :: l2)) ≡ rev (x :: l2) ++ rev l1
      t' = revIsHom l1 (x :: l2)
      t : (rev (l1 ++ (x :: l2)) ++ [ w ]) ≡ ((rev l2 ++ [ x ]) ++ rev l1) ++ [ w ]
      t = applyEquality (λ r → r ++ [ w ]) {rev (l1 ++ (x :: l2))} {((rev l2) ++ [ x ]) ++ rev l1} (transitivity t' (applyEquality (λ r → r ++ rev l1) {rev l2 ++ (x :: [])} {rev l2 ++ (x :: [])} refl))

  revRevIsId : {a : _} → {A : Set a} → (l : List A) → (rev (rev l) ≡ l)
  revRevIsId [] = refl
  revRevIsId (x :: l) = t
    where
      s : rev (rev l ++ [ x ] ) ≡ [ x ] ++ rev (rev l)
      s = revIsHom (rev l) [ x ]
      t : rev (rev l ++ [ x ] ) ≡ [ x ] ++ l
      t = identityOfIndiscernablesRight _≡_ s (applyEquality (λ n → [ x ] ++ n) (revRevIsId l))

  fold : {a b : _} {A : Set a} {B : Set b} (f : A → B → B) → B → List A → B
  fold f default [] = default
  fold f default (x :: l) = f x (fold f default l)

  map : {a : _} → {b : _} → {A : Set a} → {B : Set b} → (f : A → B) → List A → List B
  map f [] = []
  map f (x :: list) = (f x) :: (map f list)

  map' : {a : _} → {b : _} → {A : Set a} → {B : Set b} → (f : A → B) → List A → List B
  map' f = fold (λ a → (f a) ::_ ) []

  map=map' : {a : _} → {b : _} → {A : Set a} → {B : Set b} → (f : A → B) → (l : List A) → (map f l ≡ map' f l)
  map=map' f [] = refl
  map=map' f (x :: l) with map=map' f l
  ... | bl = applyEquality (f x ::_) bl

  flatten : {a : _} {A : Set a} → (l : List (List A)) → List A
  flatten [] = []
  flatten (l :: ls) = l ++ flatten ls

  flatten' : {a : _} {A : Set a} → (l : List (List A)) → List A
  flatten' = fold _++_ []

  flatten=flatten' : {a : _} {A : Set a} (l : List (List A)) → flatten l ≡ flatten' l
  flatten=flatten' [] = refl
  flatten=flatten' (l :: ls) = applyEquality (l ++_) (flatten=flatten' ls)

  length : {a : _} {A : Set a} (l : List A) → ℕ
  length [] = zero
  length (x :: l) = succ (length l)

  length' : {a : _} {A : Set a} → (l : List A) → ℕ
  length' = fold (λ _ → succ) 0

  length=length' : {a : _} {A : Set a} (l : List A) → length l ≡ length' l
  length=length' [] = refl
  length=length' (x :: l) = applyEquality succ (length=length' l)

  total : List ℕ → ℕ
  total [] = zero
  total (x :: l) = x +N total l

  total' : List ℕ → ℕ
  total' = fold _+N_ 0

  lengthConcat : {a : _} {A : Set a} (l1 l2 : List A) → length (l1 ++ l2) ≡ length l1 +N length l2
  lengthConcat [] l2 = refl
  lengthConcat (x :: l1) l2 = applyEquality succ (lengthConcat l1 l2)

  lengthFlatten : {a : _} {A : Set a} (l : List (List A)) → length (flatten l) ≡ total (map length l)
  lengthFlatten [] = refl
  lengthFlatten (l :: ls) rewrite lengthConcat l (flatten ls) | lengthFlatten ls = refl

  lengthMap : {a b : _} {A : Set a} {B : Set b} → (l : List A) → {f : A → B} → length l ≡ length (map f l)
  lengthMap [] {f} = refl
  lengthMap (x :: l) {f} rewrite lengthMap l {f} = refl

  mapMap : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → (l : List A) → {f : A → B} {g : B → C} → map g (map f l) ≡ map (g ∘ f) l
  mapMap [] = refl
  mapMap (x :: l) {f = f} {g} rewrite mapMap l {f} {g} = refl

  mapExtension : {a b : _} {A : Set a} {B : Set b} (l : List A) (f g : A → B) → ({x : A} → (f x ≡ g x)) → map f l ≡ map g l
  mapExtension [] f g pr = refl
  mapExtension (x :: l) f g pr rewrite mapExtension l f g pr | pr {x} = refl

  replicate : {a : _} {A : Set a} (n : ℕ) (x : A) → List A
  replicate zero x = []
  replicate (succ n) x = x :: replicate n x

  allTrue : {a b : _} {A : Set a} (f : A → Set b) (l : List A) → Set b
  allTrue f [] = True'
  allTrue f (x :: l) = f x && allTrue f l

  allTrueConcat : {a b : _} {A : Set a} (f : A → Set b) (l m : List A) → allTrue f l → allTrue f m → allTrue f (l ++ m)
  allTrueConcat f [] m fl fm = fm
  allTrueConcat f (x :: l) m (fst ,, snd) fm = fst ,, allTrueConcat f l m snd fm

  allTrueFlatten : {a b : _} {A : Set a} (f : A → Set b) (l : List (List A)) → allTrue (λ i → allTrue f i) l → allTrue f (flatten l)
  allTrueFlatten f [] pr = record {}
  allTrueFlatten f ([] :: ls) pr = allTrueFlatten f ls (_&&_.snd pr)
  allTrueFlatten f ((x :: l) :: ls) ((fx ,, fl) ,, snd) = fx ,, allTrueConcat f l (flatten ls) fl (allTrueFlatten f ls snd)

  allTrueMap : {a b c : _} {A : Set a} {B : Set b} (pred : B → Set c) (f : A → B) (l : List A) → allTrue (pred ∘ f) l → allTrue pred (map f l)
  allTrueMap pred f [] pr = record {}
  allTrueMap pred f (x :: l) pr = _&&_.fst pr ,, allTrueMap pred f l (_&&_.snd pr)

  allTrueExtension : {a b : _} {A : Set a} (f g : A → Set b) (l : List A) → ({x : A} → f x → g x) → allTrue f l → allTrue g l
  allTrueExtension f g [] pred t = record {}
  allTrueExtension f g (x :: l) pred (fg ,, snd) = pred {x} fg ,, allTrueExtension f g l pred snd

  allTrueTail : {a b : _} {A : Set a} (pred : A → Set b) (x : A) (l : List A) → allTrue pred (x :: l) → allTrue pred l
  allTrueTail pred x l (fst ,, snd) = snd

  head : {a : _} {A : Set a} (l : List A) (pr : 0 <N length l) → A
  head [] (le x ())
  head (x :: l) pr = x

  lengthRev : {a : _} {A : Set a} (l : List A) → length (rev l) ≡ length l
  lengthRev [] = refl
  lengthRev (x :: l) rewrite lengthConcat (rev l) (x :: []) | lengthRev l | Semiring.commutative ℕSemiring (length l) 1 = refl
