{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers

module Examples.StreamDContainer  where

-- Stream as directed container --


StreamDCon : DContainer
StreamDCon = record { Shape = ⊤; Pos = λ _ → Nat; _↓_ = _↓_; o = o; _⊕_ = λ {s} → _⊕_ {s}; ax1 = ax1; ax2 = λ {s} {p} {p'} → ax2 {s} {p} {p'} ; ax3 = ax3; ax4 = λ {s} → ax4 {s}; ax5 = ax5} where
  _↓_ : ⊤ → Nat → ⊤
  s ↓ p = s

  o : Nat
  o = zero

  ax1 : {s : ⊤} → s ↓ o == s
  ax1 = refl

  _⊕_ : {s : ⊤} → (p : Nat) → Nat → Nat
  _⊕_ zero p' = p'
  _⊕_ {s} (suc p) p' = suc (_⊕_ {s} p p')

  ax2 : {s : ⊤} → {p : Nat} → {p' : Nat} → s ↓ (_⊕_ {s} p p') == s ↓ p ↓ p'
  ax2 = refl

  ax3 : {s : ⊤} → (p : Nat) → _⊕_ {s} p o == p
  ax3 zero = refl
  ax3 {s} (suc p) = cong suc (ax3 {s} p)

  ax4 : {s : ⊤} → (p : Nat) → _⊕_ {s} o p == p -- subst (λ _ → Nat) p refl  -- (ax1' {t})
  ax4 _ = refl

  ax5 : {s : ⊤} → (p : Nat) → (p' : Nat) → (p'' : Nat) → _⊕_ {s} (_⊕_ {s} p p') p'' == _⊕_ {s} p (_⊕_ {s} p' p'')
  ax5 zero p' p'' = refl
  ax5 (suc p) p' p'' = cong suc (ax5 p p' p'')

  infixl 50 _↓_
  infixl 60 _⊕_
