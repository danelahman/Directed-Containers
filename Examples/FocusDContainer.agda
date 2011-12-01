{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers
open import Containers

module Examples.FocusDContainer  where

-- Focused directed container based on an undirected container--

FocusedDCon : Container → DContainer
FocusedDCon (S ◁ P) = record { Shape = Shape ; Pos = Pos ; _↓_ = _↓_ ; o = λ {s} → o {s} ; _⊕_ = λ {s} → _⊕_ {s} ; ax1 = refl ; ax2 = refl ; ax3 = λ p → refl ; ax4 = λ p → refl ; ax5 = λ p p' p'' → refl } where
  Shape : Set
  Shape = ∃ S P
  Pos : ∃ S P → Set
  Pos (s , p) = P s
  _↓_ : (s : ∃ S P) → P (∃.fst∃ s) → ∃ S P
  (s , p) ↓ p' = s , p'
  o : {s : ∃ S P} → P (∃.fst∃ s)
  o {(s , p)} = p
  _⊕_ : {s : ∃ S P} → (p : P (∃.fst∃ s)) → P (∃.fst∃ s) → P (∃.fst∃ s)
  p ⊕ p' = p'

  infixl 50 _↓_
  infixl 60 _⊕_
