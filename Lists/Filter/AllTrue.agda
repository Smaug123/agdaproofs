{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Functions.Definition
open import Lists.Definition
open import Lists.Monad
open import Boolean.Definition

module Lists.Filter.AllTrue where

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

filter : {a : _} {A : Set a} (l : List A) (f : A → Bool) → List A
filter [] f = []
filter (x :: l) f with f x
filter (x :: l) f | BoolTrue = x :: filter l f
filter (x :: l) f | BoolFalse = filter l f
