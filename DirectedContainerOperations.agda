{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers
open import StrictDirectedContainer

module DirectedContainerOperations  where

open DContainer
open Monoid

_+'_ : DContainer → DContainer → DContainer
(_◁_ Shape₀ Pos₀ _↓₀_ o₀ _⊕₀_ ax1₀ ax2₀ ax3₀ ax4₀ ax5₀) +' (_◁_ Shape₁ Pos₁ _↓₁_ o₁ _⊕₁_ ax1₁ ax2₁ ax3₁ ax4₁ ax5₁) = _◁_ Shape₂ Pos₂ _↓₂_ (λ {s} → _o₂_ {s}) (λ {s} → _⊕₂_ {s}) ax1₂ ax2₂ (λ {s} → ax3₂ {s}) (λ {s} → ax4₂ {s}) (λ {s} → ax5₂ {s}) where
  Shape₂ : Set
  Shape₂ = Shape₀ + Shape₁
  Pos₂ : Shape₀ + Shape₁ → Set
  Pos₂ (inl s) = Pos₀ s
  Pos₂ (inr s) = Pos₁ s
  _↓₂_ : (s : Shape₀ + Shape₁) → Pos₂ s → Shape₀ + Shape₁
  _↓₂_ (inl s) p = inl (s ↓₀ p)
  _↓₂_ (inr s) p = inr (s ↓₁ p)
  _o₂_ : {s : Shape₀ + Shape₁} → Pos₂ s
  _o₂_ {inl s} = o₀
  _o₂_ {inr s} = o₁
  _⊕₂_ : {s : Shape₀ + Shape₁} → (p : Pos₂ s) → Pos₂ (s ↓₂ p) → Pos₂ s
  _⊕₂_ {inl s} p p' = p ⊕₀ p'
  _⊕₂_ {inr s} p p' = p ⊕₁ p'
  ax1₂ : {s : Shape₀ + Shape₁} → s ↓₂ (_o₂_ {s}) == s
  ax1₂ {inl s} = cong inl ax1₀
  ax1₂ {inr s} = cong inr ax1₁
  ax2₂ : {s : Shape₀ + Shape₁} → {p : Pos₂ s} → {p' : Pos₂ (s ↓₂ p)} → s ↓₂ (_⊕₂_ {s} p p') == (s ↓₂ p) ↓₂ p'
  ax2₂ {inl s} = cong inl ax2₀
  ax2₂ {inr s} = cong inr ax2₁
  ax3₂ : {s : Shape₀ + Shape₁} → (p : Pos₂ s) → _⊕₂_ {s} p (_o₂_ {s ↓₂ p}) == p
  ax3₂ {inl s} p = ax3₀ p
  ax3₂ {inr s} p = ax3₁ p
  ax4₂ : {s : Shape₀ + Shape₁} → (p : Pos₂ (s ↓₂ (_o₂_ {s}))) → _⊕₂_ {s} (_o₂_ {s}) p == p
  ax4₂ {inl s} p = trans (ax4₀ p) refl
  ax4₂ {inr s} p = trans (ax4₁ p) refl
  ax5₂ : {s : Shape₀ + Shape₁} → (p : Pos₂ s) → (p' : Pos₂ (s ↓₂ p)) → (p'' : Pos₂ (s ↓₂ (_⊕₂_ {s} p p'))) → _⊕₂_ {s} (_⊕₂_ {s} p p') p'' == _⊕₂_ {s} p (_⊕₂_ {s ↓₂ p} p' (subst Pos₂ p'' (ax2₂ {s} {p} {p'})))
  ax5₂ {inl s} p p' p'' = trans (ax5₀ p p' p'') (cong (λ t → (p ⊕₀ (p' ⊕₀ t))) (substcong Pos₂ inl p'' ax2₀))
  ax5₂ {inr s} p p' p'' = trans (ax5₁ p p' p'') (cong ((λ t → (p ⊕₁ (p' ⊕₁ t)))) (substcong Pos₂ inr p'' ax2₁))
  infixl 50 _↓₂_

open StrictDContainer₁ renaming (Shape to Shape')
open StrictDContainer₂ renaming (Pos to Pos' ; o to o' ; _↓_ to _↓'_ ; C₁ to C₁')
open StrictDContainer₃ renaming (_⊕_ to _⊕'_)
open StrictDContainer renaming (ax1 to ax1' ; ax2 to ax2' ; ax3 to ax3' ; ax4 to ax4' ; ax5 to ax5' ; ax6 to ax6' )


monoid-exp' : Monoid → StrictDContainer
monoid-exp' (monoid M e _*_ assoc-ax id-ax1 id-ax2) = _◁_ C₃' refl refl refl (λ {s} {p} {p'} {p''} → h.ax4'' {s} {p} {p'} {p''}) refl (sym (assoc-ax _ _ _)) where
  C₃' : StrictDContainer₃
  C₃' = _◁₃_ C₂' _⊕+'_ module h where
    C₂' : StrictDContainer₂
    C₂' = _◁₂_ C₁'' module h' where
      C₁'' : StrictDContainer₁
      C₁'' = _◁₁_ ⊤ (λ _ → M) (λ _ _ → tt)
    _⊕+'_ : {s : ⊤} (p : Maybe M) → M → M
    nothing ⊕+' p' = p'
    just p ⊕+' p' = p * p'
    ax4'' : {s : ⊤} {p p' : Maybe M} {p'' : M} → _⊕+'_ (((_◁₂_ ((⊤ ◁₁ λ _ → M) (λ _ _ → tt)) ◁₃ λ {s} → _⊕+'_) ⊕' p) p') p'' == _⊕+'_ p (_⊕+'_ p' p'')
    ax4'' {s} {nothing} {nothing} = refl
    ax4'' {s} {nothing} {just p'} = refl
    ax4'' {s} {just p} {nothing} = refl
    ax4'' {s} {just p} {just p'} {p''} = assoc-ax p p' p''

monoid-exp : Monoid → DContainer
monoid-exp Mon = SDC2DC (monoid-exp' Mon)