{-# OPTIONS --safe --warning=error --without-K #-}

open import LogicalFormulae
open import Lists.Definition
open import Lists.Fold.Fold
open import Lists.Concat
open import Lists.Length
open import Numbers.Naturals.Semiring

module Lists.Monad where

open import Lists.Map.Map public

flatten : {a : _} {A : Set a} → (l : List (List A)) → List A
flatten [] = []
flatten (l :: ls) = l ++ flatten ls

flatten' : {a : _} {A : Set a} → (l : List (List A)) → List A
flatten' = fold _++_ []

flatten=flatten' : {a : _} {A : Set a} (l : List (List A)) → flatten l ≡ flatten' l
flatten=flatten' [] = refl
flatten=flatten' (l :: ls) = applyEquality (l ++_) (flatten=flatten' ls)

lengthFlatten : {a : _} {A : Set a} (l : List (List A)) → length (flatten l) ≡ (fold _+N_ zero (map length l))
lengthFlatten [] = refl
lengthFlatten (l :: ls) rewrite lengthConcat l (flatten ls) | lengthFlatten ls = refl

flattenConcat : {a : _} {A : Set a} (l1 l2 : List (List A)) → flatten (l1 ++ l2) ≡ (flatten l1) ++ (flatten l2)
flattenConcat [] l2 = refl
flattenConcat (l1 :: ls) l2 rewrite flattenConcat ls l2 | concatAssoc l1 (flatten ls) (flatten l2) = refl

pure : {a : _} {A : Set a} → A → List A
pure a = [ a ]

bind : {a b : _} {A : Set a} {B : Set b} → (f : A → List B) → List A → List B
bind f l = flatten (map f l)

private
  leftIdentLemma : {a : _} {A : Set a} (xs : List A) → flatten (map pure xs) ≡ xs
  leftIdentLemma [] = refl
  leftIdentLemma (x :: xs) rewrite leftIdentLemma xs = refl

leftIdent : {a b : _} {A : Set a} {B : Set b} → (f : A → List B) → {x : A} → bind pure (f x) ≡ f x
leftIdent f {x} with f x
leftIdent f {x} | [] = refl
leftIdent f {x} | y :: ys rewrite leftIdentLemma ys = refl

rightIdent : {a b : _} {A : Set a} {B : Set b} → (f : A → List B) → {x : A} → bind f (pure x) ≡ f x
rightIdent f {x} with f x
rightIdent f {x} | [] = refl
rightIdent f {x} | y :: ys rewrite appendEmptyList ys = refl

associative : {a b c : _} {A : Set a} {B : Set b} {C : Set c} → (f : A → List B) (g : B → List C) → {x : List A} → bind g (bind f x) ≡ bind (λ a → bind g (f a)) x
associative f g {[]} = refl
associative f g {x :: xs} rewrite mapConcat (f x) (flatten (map f xs)) g | flattenConcat (map g (f x)) (map g (flatten (map f xs))) = applyEquality (flatten (map g (f x)) ++_) (associative f g {xs})
