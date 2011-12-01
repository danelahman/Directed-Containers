{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers

module Examples.BinaryTreeDContainer1  where

-- Binary tree as directed container --

data Choice : Set where
  lc : Choice
  rc : Choice

InfBTreeDCon : DContainer
InfBTreeDCon = record { Shape = ⊤ ; Pos = λ x → List Choice ; _↓_ = _↓_ ; o = λ {s} → o {s} ; _⊕_ = λ {s} → _⊕_ {s} ; ax1 = ax1 ; ax2 = λ {s} {p} {p'} → ax2 {s} {p} {p'} ; ax3 = ax3 ; ax4 = λ {s} → ax4 {s} ; ax5 = ax5 } where
  _↓_ : (s : ⊤) → List Choice → ⊤
  s ↓ p = s

  o : {s : ⊤} → List Choice
  o = nil

  _⊕_ : {s : ⊤} → List Choice → List Choice → List Choice
  _⊕_ nil p' = p'
  _⊕_ {s} (cons p ps) p' = cons p (_⊕_ {s} ps p')

  ax1 : {s : ⊤} → s ↓ o {s} == s
  ax1 = refl

  ax2 : {s : ⊤} → {p : List Choice} → {p' : List Choice} → s ↓ (_⊕_ {s} p p') == s ↓ p ↓ p'
  ax2 = refl
  
  ax3 : {s : ⊤} → (p : List Choice) → _⊕_ {s} p (o {s}) == p
  ax3 nil = refl
  ax3 (cons p ps) = cong (cons p) (ax3 ps)

  ax4 : {s : ⊤} → (p : List Choice) → _⊕_ {s} (o {s}) p == p
  ax4 p = refl

  ax5 : {s : ⊤} → (p : List Choice) → (p' : List Choice) → (p'' : List Choice) → _⊕_ {s} (_⊕_ {s} p p') p'' == _⊕_ {s} p (_⊕_ {s} p' p'')
  ax5 nil p' p'' = refl
  ax5 (cons p ps) p' p'' = cong (cons p) (ax5 ps p' p'')

  infixl 50 _↓_
  infixl 60 _⊕_
