{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers
open import Examples.FocusDContainer
open import Containers

module Examples.BinaryTreeDContainer2  where

-- Binary tree as directed container --

data TreeShape : Set where
  nd : Maybe TreeShape → Maybe TreeShape → TreeShape

data TreePos : TreeShape → Set where
  stop : ∀ {s} → TreePos (s)
  left : ∀ {l r} → TreePos l → TreePos (nd (just l) r)
  right : ∀ {l r} → TreePos r → TreePos (nd l (just r))

FinBTreeDCon : DContainer
FinBTreeDCon = record { Shape = TreeShape ; Pos = TreePos ; _↓_ = _↓_ ; o = o ; _⊕_ = _⊕_ ; ax1 = ax1 ; ax2 = λ {s} → ax2 {s} ; ax3 = ax3 ; ax4 = λ {s} → ax4 {s} ; ax5 = ax5 } where
  _↓_ : (s : TreeShape) → TreePos s → TreeShape
  s ↓ stop = s
  nd .(just l) r ↓ left {l} p = l ↓ p
  nd l .(just r) ↓ right {.l} {r} p = r ↓ p

  o : {s : TreeShape} → TreePos s
  o {nd l r} = stop

  _⊕_ : {s : TreeShape} → (p : TreePos s) → TreePos (s ↓ p) → TreePos s
  _⊕_ {nd l r} stop p' = p'
  _⊕_ {nd (just l) r} (left p) p' = left (p ⊕ p')
  _⊕_ {nd l (just r)} (right p) p' = right (p ⊕ p')

  ax1 : {s : TreeShape} → s ↓ o == s
  ax1 {nd l r} = refl

  ax2 : {s : TreeShape} → {p : TreePos s} → {p' : TreePos (s ↓ p)} → s ↓ p ⊕ p' == s ↓ p ↓ p'
  ax2 {nd l r} {stop} = refl
  ax2 {nd (just l) r} {left p} {p'} = ax2 {l}
  ax2 {nd l (just r)} {right p} {p'} = ax2 {r}

  ax3 : {s : TreeShape} → (p : TreePos s) → p ⊕ o == p
  ax3 {nd l r} stop = refl
  ax3 {nd (just l) r} (left p) = cong left (ax3 p)
  ax3 {nd l (just r)} (right p) = cong right (ax3 p)

  ax4 : {s : TreeShape} → (p : TreePos (s ↓ o)) → _⊕_ {s} o p == p --subst TreePos p ax1
  ax4 {nd l r} p = refl

  f2 : {s : TreeShape} → {p : TreePos s} → {p' : TreePos (s ↓ p)} → TreePos(s ↓ p ⊕ p') → TreePos(s ↓ p ↓ p')
  f2 {s} {p} {p'} p'' = subst TreePos p'' (ax2 {s})

  ax5 : {s : TreeShape} → (p : TreePos s) → (p' : TreePos (s ↓ p)) → (p'' : TreePos (s ↓ p ⊕ p')) → p ⊕ p' ⊕ p'' == p ⊕ (p' ⊕ (f2 {s} {p} {p'} p''))
  ax5 {nd l r} stop p' p'' = refl
  ax5 {nd (just l) r} (left p) p' p'' = cong left (ax5 p p' p'')
  ax5 {nd l (just r)} (right p) p' p'' = cong right (ax5 p p' p'')

  infixl 50 _↓_
  infixl 60 _⊕_

FocusedTreeDCon : DContainer
FocusedTreeDCon = FocusedDCon (TreeShape ◁ TreePos)
