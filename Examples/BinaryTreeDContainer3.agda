{-# OPTIONS --type-in-type #-}

open import Utils
open import DContainers
open import Examples.FocusDContainer
open import Containers

module Examples.BinaryTreeDContainer3  where

data TreeShape : Set where
  leaf : TreeShape
  node : TreeShape → TreeShape → TreeShape

data TreePos : TreeShape → Set where
  stop : ∀{s} → TreePos s
  left : ∀{l r} → TreePos l → TreePos (node l r)
  right : ∀{l r} → TreePos r → TreePos (node l r)

FinBTreeDCon : DContainer
FinBTreeDCon = record {
  Shape = TreeShape;
  Pos = TreePos;
  _↓_ = _↓_; 
  o   = o;
  _⊕_ = _⊕_; 
  ax1 = refl; 
  ax2 = λ{s}{p} → ax2 {s}{p};
  ax3 = ax3; 
  ax4 = λ _ → refl; 
  ax5 = ax5} 
  where
  _↓_ : (s : TreeShape) → TreePos s → TreeShape
  s ↓ stop = s
  .(node l r) ↓ left  {l} {r} p = l ↓ p
  .(node l r) ↓ right {l} {r} p = r ↓ p  

  o : ∀{s} → TreePos s
  o = stop

  _⊕_ : ∀{s}(p : TreePos s) → TreePos (s ↓ p) → TreePos s
  stop    ⊕ p' = p'
  left  p ⊕ p' = left (p ⊕ p')
  right p ⊕ p' = right (p ⊕ p')
  
  ax1 : {s : TreeShape} → s ↓ o == s
  ax1 = refl

  ax2 : {s : TreeShape} → {p : TreePos s} → {p' : TreePos (s ↓ p)} → s ↓ p ⊕ p' == s ↓ p ↓ p'
  ax2 {s}           {stop}           = refl
  ax2 {.(node l r)} {left  {l}{r} p} = ax2 {l} {p}
  ax2 {.(node l r)} {right {l}{r} p} = ax2 {r} {p}

  ax3 : {s : TreeShape} → (p : TreePos s) → p ⊕ o == p
  ax3 stop      = refl
  ax3 (left  p) = cong left (ax3 p)
  ax3 (right p) = cong right (ax3 p)

  f2 : {s : TreeShape} → {p : TreePos s} → {p' : TreePos (s ↓ p)} → TreePos(s ↓ p ⊕ p') → TreePos(s ↓ p ↓ p')
  f2 {s} {p} {p'} p'' = subst TreePos p'' (ax2 {s} {p})

  ax5 : {s : TreeShape} → (p : TreePos s) → (p' : TreePos (s ↓ p)) → (p'' : TreePos (s ↓ p ⊕ p')) → 
        p ⊕ p' ⊕ p'' == p ⊕ (p' ⊕ (f2 {s} {p} {p'} p''))
  ax5 stop      p' p'' = refl
  ax5 (left  p) p' p'' = cong left (ax5 p p' p'')
  ax5 (right p) p' p'' = cong right (ax5 p p' p'')

  infixl 50 _↓_
  infixl 60 _⊕_
