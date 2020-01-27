{-# OPTIONS --safe --warning=error #-}

open import Numbers.Naturals.Semiring
open import Numbers.Naturals.Order
open import Sets.FinSet.Definition
open import LogicalFormulae
open import Numbers.Naturals.WithK
open import Sets.FinSet.Lemmas

module Sets.FinSetWithK where

private
  sgEq : {l m : _} {L : Set l} → {pr : L → Set m} → {a b : Sg L pr} → (underlying a ≡ underlying b) → ({c : L} → (r s : pr c) → r ≡ s) → (a ≡ b)
  sgEq {l} {m} {L} {prop} {(a , b1)} {(.a , b)} refl pr2 with pr2 {a} b b1
  sgEq {l} {m} {L} {prop} {(a , b1)} {(.a , .b1)} refl pr2 | refl = refl

finNotEqualsRefl : {n : ℕ} {a b : FinSet (succ n)} → (p1 p2 : FinNotEquals a b) → p1 ≡ p2
finNotEqualsRefl {.1} {.fzero} {.(fsucc fzero)} (fne2 .fzero .(fsucc fzero) (inl (refl ,, refl))) (fne2 .fzero .(fsucc fzero) (inl (refl ,, refl))) = refl
finNotEqualsRefl {.1} {.fzero} {.(fsucc fzero)} (fne2 .fzero .(fsucc fzero) (inl (refl ,, refl))) (fne2 .fzero .(fsucc fzero) (inr (() ,, snd)))
finNotEqualsRefl {.1} {.(fsucc fzero)} {.fzero} (fne2 .(fsucc fzero) .fzero (inr (refl ,, refl))) (fne2 .(fsucc fzero) .fzero (inl (() ,, snd)))
finNotEqualsRefl {.1} {.(fsucc fzero)} {.fzero} (fne2 .(fsucc fzero) .fzero (inr (refl ,, refl))) (fne2 .(fsucc fzero) .fzero (inr (refl ,, refl))) = refl
finNotEqualsRefl {.(succ (succ _))} {.fzero} {.(fsucc a)} (fneN .fzero .(fsucc a) (inl (inl (refl ,, (a , refl))))) (fneN .fzero .(fsucc a) (inl (inl (refl ,, (.a , refl))))) = refl
finNotEqualsRefl {.(succ (succ _))} {.fzero} {.(fsucc a)} (fneN .fzero .(fsucc a) (inl (inl (refl ,, (a , refl))))) (fneN .fzero .(fsucc a) (inl (inr ((a₁ , ()) ,, snd))))
finNotEqualsRefl {.(succ (succ _))} {.fzero} {.(fsucc a)} (fneN .fzero .(fsucc a) (inl (inl (refl ,, (a , refl))))) (fneN .fzero .(fsucc a) (inr ((fst ,, snd) , b))) = exFalso q
  where
    p : fzero ≡ fsucc fst
    p = _&_&_.one b
    q : False
    q with p
    ... | ()
finNotEqualsRefl {.(succ (succ _))} {.(fsucc a)} {.fzero} (fneN .(fsucc a) .fzero (inl (inr ((a , refl) ,, refl)))) (fneN .(fsucc a) .fzero (inl (inl (() ,, snd))))
finNotEqualsRefl {.(succ (succ _))} {.(fsucc a)} {.fzero} (fneN .(fsucc a) .fzero (inl (inr ((a , refl) ,, refl)))) (fneN .(fsucc a) .fzero (inl (inr ((.a , refl) ,, refl)))) = refl
finNotEqualsRefl {.(succ (succ _))} {.(fsucc a)} {.fzero} (fneN .(fsucc a) .fzero (inl (inr ((a , refl) ,, refl)))) (fneN .(fsucc a) .fzero (inr ((fst ,, snd) , b))) = exFalso q
  where
    p : fzero ≡ fsucc snd
    p = _&_&_.two b
    q : False
    q with p
    ... | ()
finNotEqualsRefl {.(succ (succ _))} {a} {b} (fneN a b (inr (record { fst = fst ; snd = snd₁ } , snd))) (fneN .a .b (inl (inl (fst1 ,, snd₂)))) = exFalso q
  where
    p : fzero ≡ fsucc fst
    p = transitivity (equalityCommutative fst1) (_&_&_.one snd)
    q : False
    q with p
    ... | ()
finNotEqualsRefl {.(succ (succ _))} {a} {b} (fneN a b (inr (record { fst = fst ; snd = snd1 } , snd))) (fneN .a .b (inl (inr (fst₁ ,, snd2)))) = exFalso q
  where
    p : fzero ≡ fsucc snd1
    p = transitivity (equalityCommutative snd2) (_&_&_.two snd)
    q : False
    q with p
    ... | ()
finNotEqualsRefl {.(succ (succ _))} {.fzero} {b} (fneN fzero b (inr (record { fst = fst ; snd = snd₁ } , snd))) (fneN .fzero .b (inr ((fst1 ,, snd₂) , b1))) = exFalso q
  where
    p : fzero ≡ fsucc fst1
    p = _&_&_.one b1
    q : False
    q with p
    ... | ()
finNotEqualsRefl {.(succ (succ _))} {.(fsucc a)} {.fzero} (fneN (fsucc a) fzero (inr (record { fst = fst ; snd = snd₁ } , snd))) (fneN .(fsucc a) .fzero (inr ((fst₁ ,, snd2) , b1))) = exFalso q
  where
    p : fzero ≡ fsucc snd2
    p = _&_&_.two b1
    q : False
    q with p
    ... | ()
finNotEqualsRefl {.(succ (succ _))} {.(fsucc a)} {.(fsucc b)} (fneN (fsucc a) (fsucc b) (inr (record { fst = fst ; snd = snd1 } , snd))) (fneN .(fsucc a) .(fsucc b) (inr ((fst1 ,, snd2) , b1))) = ans
  where
    t : a ≡ fst1
    t = fsuccInjective (_&_&_.one b1)
    t' : a ≡ fst
    t' = fsuccInjective (_&_&_.one snd)
    u : b ≡ snd1
    u = fsuccInjective (_&_&_.two snd)
    u' : b ≡ snd2
    u' = fsuccInjective (_&_&_.two b1)
    equality : {c : FinSet (succ (succ _)) && FinSet (succ (succ _))} → (r1 s : (fsucc a ≡ fsucc (_&&_.fst c)) & (fsucc b ≡ fsucc (_&&_.snd c)) & FinNotEquals (_&&_.fst c) (_&&_.snd c)) → r1 ≡ s
    equality record { one = refl ; two = refl ; three = q } record { one = refl ; two = refl ; three = q' } = applyEquality (λ t → record { one = refl ; two = refl ; three = t }) (finNotEqualsRefl q q')
    r : (fst ,, snd1) ≡ (fst1 ,, snd2)
    r rewrite equalityCommutative t | equalityCommutative t' | equalityCommutative u | equalityCommutative u' = refl
    ans : fneN (fsucc a) (fsucc b) (inr ((fst ,, snd1) , snd)) ≡ fneN (fsucc a) (fsucc b) (inr ((fst1 ,, snd2) , b1))
    ans = applyEquality (λ t → fneN (fsucc a) (fsucc b) (inr t)) (sgEq r equality)
