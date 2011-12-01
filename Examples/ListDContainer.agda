{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers

module Examples.ListDContainer  where

-- Nonempty list as directed container --

ListDCon : DContainer
ListDCon = record { Shape = Nat; Pos = λ n → Fin (suc n); _↓_ = _↓_; o = o; _⊕_ = _⊕_; ax1 = ax1; ax2 = λ {n} → ax2 {n} ; ax3 = ax3; ax4 = λ {n} → ax4 {n}; ax5 = ax5} where
  _↓_ : (n : Nat) → Fin (suc n) → Nat
  zero ↓ _ = zero
  suc n ↓ zero = suc n
  suc n ↓ suc n' = n ↓ n'

  o : {n : Nat} → Fin (suc n)
  o = zero

  ax1 : {n : Nat} → n ↓ o == n
  ax1 {zero} = refl
  ax1 {suc n} = refl

  f1' : {n : Nat} → Fin (suc (n ↓ o)) → Fin (suc n)
  f1' {n} p = subst (λ n → Fin (suc n)) p (ax1)

  _⊕_ : {n : Nat} → (p : Fin (suc n)) → Fin (suc (n ↓ p)) → Fin (suc n)
  _⊕_ {zero} _ p' = p'
  _⊕_ {suc n} zero p' = p'
  _⊕_ {suc n} (suc p) p' = suc (p ⊕ p')

  ax2 : {n : Nat} → {p : Fin (suc n)} → {p' : Fin (suc (n ↓ p))} → n ↓ p ⊕ p' == n ↓ p ↓ p'
  ax2 {zero} {_} = refl
  ax2 {suc n} {zero} = refl
  ax2 {suc n} {suc p} = ax2 {n} {p}

  f2 : {n : Nat} → {p : Fin (suc n)} → {p' : Fin (suc (n ↓ p))} → Fin (suc (n ↓ p ⊕ p')) → Fin (suc (n ↓ p ↓ p'))
  f2 {n} {p} {p'} p'' = subst (λ n → Fin (suc n)) p'' (ax2 {n})

  ax3 : {n : Nat} → (p : Fin (suc n)) → p ⊕ o == p
  ax3 {zero} zero = refl
  ax3 {suc n} zero = refl
  ax3 {zero} (suc ())
  ax3 {suc n} (suc p) = cong suc (ax3 p)
  
  --ax4 : {n : Nat} → (p : Fin (suc (n ↓ o))) → _⊕_ {n} o p == f1' p
  ax4 : {n : Nat} → (p : Fin (suc (n ↓ o))) → _⊕_ {n} o p == p
  ax4 {zero} p = refl
  ax4 {suc y} p = refl

  ax5 : {n : Nat} → (p : Fin (suc n)) → (p' : Fin (suc (n ↓ p))) → (p'' : Fin (suc (n ↓ p ⊕ p'))) → p ⊕ p' ⊕ p'' == p ⊕ (p' ⊕ f2 {n} {p} {p'} p'')
  ax5 {zero} zero p' p'' = refl
  ax5 {zero} (suc ()) p' p''
  ax5 {suc n} zero p' p'' = refl
  ax5 {suc n} (suc p) p' p'' = cong suc (ax5 p p' p'')

  infixl 50 _↓_
  infixl 60 _⊕_
