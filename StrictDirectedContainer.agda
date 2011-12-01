{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers

module StrictDirectedContainer  where

record StrictDContainer₁ : Set where
  constructor _◁₁_
  field Shape : Set
        Pos+ : Shape → Set
        _↓+_ : (s : Shape) → Pos+ s → Shape


record StrictDContainer₂ : Set where
  constructor _◁₂_
  field C₁ : StrictDContainer₁

  open StrictDContainer₁

  Pos : Shape C₁ → Set
  Pos s = Maybe (Pos+ C₁ s)

  _↓_ : (s : Shape C₁) → Pos s → Shape C₁
  _↓_ s nothing = s
  _↓_ s (just mp) = _↓+_ C₁ s mp

  o : {s : Shape C₁} → Pos s
  o = nothing

record StrictDContainer₃ : Set where
  constructor _◁₃_
  field C₂ : StrictDContainer₂

  open StrictDContainer₁
  open StrictDContainer₂

  field _⊕+_ : {s : Shape (C₁ C₂)} → (p : Pos C₂ s) → Pos+ (C₁ C₂) (_↓_ C₂ s p) → Pos+ (C₁ C₂) s

  _⊕_ : {s : Shape (C₁ C₂)} → (p : Pos C₂ s) → Pos C₂ (_↓_ C₂ s p) → Pos C₂ s
  mp ⊕ nothing = mp
  mp ⊕ just mp' = just (_⊕+_ mp mp')


record StrictDContainer : Set where
  constructor _◁_
  field C₃ : StrictDContainer₃

  open StrictDContainer₁ 
  open StrictDContainer₂ 
  open StrictDContainer₃

  field ax1 : {s : Shape (C₁ (C₂ C₃))} → {p : Pos (C₂ C₃) s} → {p' : Pos (C₂ C₃) ((C₂ C₃ ↓ s) p)} → _↓_ (C₂ C₃) s ((C₃ ⊕ p) p') == _↓_ (C₂ C₃) (_↓_ (C₂ C₃) s p) p'
        
        ax2 : {s : Shape (C₁ (C₂ C₃))} → {p : Pos+ (C₁ (C₂ C₃)) (_↓_ (C₂ C₃) s (o (C₂ C₃)))} → _⊕+_ C₃ (o (C₂ C₃)) p == p
        ax3 : {s : Shape (C₁ (C₂ C₃))} → {p : Pos (C₂ C₃) s} → {p' : Pos+ (C₁ (C₂ C₃)) (_↓_ (C₂ C₃) s p)} → _↓+_ (C₁ (C₂ C₃)) s (_⊕+_ C₃ p p') == _↓+_ (C₁ (C₂ C₃)) (_↓_ (C₂ C₃) s p) p'
        ax4 : {s : Shape (C₁ (C₂ C₃))} → {p : Pos (C₂ C₃) s} → {p' : Pos (C₂ C₃) (_↓_ (C₂ C₃) s p)} → {p'' : Pos+ (C₁ (C₂ C₃)) (_↓_ (C₂ C₃) s ((C₃ ⊕ p) p'))} → _⊕+_ C₃ (_⊕_ C₃ p p') p'' == _⊕+_ C₃ p (_⊕+_ C₃ p' (subst (Pos+ (C₁ (C₂ C₃))) p'' (ax1 {s} {p} {p'})))
        
        ax5 : {s : Shape (C₁ (C₂ C₃))} → {p : Pos+ (C₁ (C₂ C₃)) s} → {p' : Pos+ (C₁ (C₂ C₃)) ((C₁ (C₂ C₃) ↓+ s) p)} → (C₁ (C₂ C₃) ↓+ s) ((C₃ ⊕+ just p) p') == (C₁ (C₂ C₃) ↓+ (C₁ (C₂ C₃) ↓+ s) p) p' 
        ax6 : {s : Shape (C₁ (C₂ C₃))} → {p : Pos+ (C₁ (C₂ C₃)) s} → {p' : Pos+ (C₁ (C₂ C₃)) ((C₁ (C₂ C₃) ↓+ s) p)} → {p'' : Pos+ (C₁ (C₂ C₃)) ((C₁ (C₂ C₃) ↓+ s) ((C₃ ⊕+ just p) p'))} → (C₃ ⊕+ just p) ((C₃ ⊕+ just p') (subst (Pos+ (C₁ (C₂ C₃))) p'' (ax1 {s} {just p} {just p'}))) == (C₃ ⊕+ just ((C₃ ⊕+ just p) p')) p'' 


open StrictDContainer₁ 
open StrictDContainer₂ 
open StrictDContainer₃
open StrictDContainer

SDC2DC : StrictDContainer → DContainer
SDC2DC (_◁_ C ax1 ax2 ax3 ax4 ax5 ax6) = _◁_ Shape' Pos' _↓'_ o' _⊕'_ ax1' (λ {s} {p} {p'} → ax2' {s} {p} {p'}) ax3' ax4' ax5' where
  Shape' : Set
  Shape' = Shape (C₁ (C₂ C))

  Pos' : Shape' → Set
  Pos' = Pos (C₂ C)

  _↓'_ : (s : Shape') → Pos' s → Shape'
  _↓'_ = _↓_ (C₂ C)

  o' : {s : Shape'} → Pos' s
  o' = o (C₂ C)

  _⊕'_ : {s : Shape'} → (p : Pos' s) → Pos' (s ↓' p) → Pos' s
  _⊕'_ = _⊕_ C

  abstract

    ax1' : {s : Shape'} → s ↓' o' == s
    ax1' = refl

    ax2' : {s : Shape'} → {p : Pos' s} → {p' : Pos' (s ↓' p)} → s ↓' p ⊕' p' == s ↓' p ↓' p'
    ax2' {s} {p} {p'} = ax1 {s} {p} {p'}

    ax3' : {s : Shape'} → (p : Pos' s) → p ⊕' o' == p
    ax3' p = refl

    ax4' : {s : Shape'} → (p : Pos' (s ↓' o')) → o' ⊕' p == p
    ax4' nothing = refl
    ax4' (just p) = cong just ax2

    ax5' : {s : Shape'} → (p : Pos' s) → (p' : Pos' (s ↓' p)) → (p'' : Pos' (s ↓' p ⊕' p')) → p ⊕' p' ⊕' p'' == p ⊕' (p' ⊕' (subst Pos' p'' (ax2' {s} {p} {p'})))
    ax5' {s} nothing nothing nothing = sym (trans (trans ((ax4' ((C ⊕ nothing) (subst Pos' nothing (ax1 {s} {nothing} {nothing}))))) (ax4' (subst Pos' nothing (ax1 {s} {nothing} {nothing})))) (stripsubst (Pos (C₂ C)) nothing (ax1 {s} {nothing} {nothing}))) 

    ax5' {s} nothing nothing (just p'') = sym (trans (trans (trans (ax4' ((C ⊕ nothing) (subst (Pos') (just p'') (ax1 {s} {nothing} {nothing})))) (ax4' (subst Pos' (just p'') (ax1 {s} {nothing} {nothing})))) (stripsubst (Pos') (just p'') (ax1 {s} {nothing} {nothing}))) (sym (cong just ax2)))

    ax5' {s} nothing (just p) nothing = sym (trans (trans (ax4' ((C ⊕ just p) (subst (Pos (C₂ C)) nothing (ax1 {s} {nothing} {just p})))) (trans (cong' {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} {subst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) nothing (ax1 {s} {nothing} {just p})} {nothing} (trans ((stripsubst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) nothing (ax1 {s} {nothing} {just p}))) (icong' (cong (C₁ (C₂ C) ↓+ s) ax2) refl {λ {s'} → nothing {Pos+ (C₁ (C₂ C)) s'}} {λ {s'} → nothing {Pos+ (C₁ (C₂ C)) s'}} refl)) refl {(C ⊕ just p)} {(C ⊕ just p)} refl) (ax3' (just p)))) (cong just (sym ax2)))

    ax5' {s} nothing (just p') (just p'') = sym (trans (ax4' ((C ⊕ just p') (subst (Pos (C₂ C)) (just p'') (ax1 {s} {nothing} {just p'})))) (trans (cong' {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p'))} {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p'))} {subst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) (just p'') (ax1 {s} {nothing} {just p'})} {just (subst (λ x → Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) x)) p'' ax2)} (trans (stripsubst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) (just p'') (ax1 {s} {nothing} {just p'})) (trans refl (cong' {Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) ((C ⊕+ nothing) p'))} {Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p')} {p''} {subst (λ x → Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) x)) p'' ax2} (sym (stripsubst (λ x → Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) x)) p'' ax2)) (ext' (λ {a} {a'} q → cong (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) ax3)) {just} {just} (icong' {Shape (C₁ (C₂ C))} {Shape (C₁ (C₂ C))} {(C₁ (C₂ C) ↓+ s) ((C ⊕+ nothing) p')} {(C₁ (C₂ C) ↓+ s) p'} ax3 refl {λ {x} → just {Pos+ (C₁ (C₂ C)) x}} {λ {x} → just {Pos+ (C₁ (C₂ C)) x}} refl)))) refl {C ⊕ just p'} {C ⊕ just p'} refl) (cong2'' {Pos+ (C₁ (C₂ C)) s} {λ x → Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) x)} {λ x → Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) x)} refl {λ a x → Maybe (Pos+ (C₁ (C₂ C)) s)} {λ a x → Maybe (Pos+ (C₁ (C₂ C)) s)} refl {λ x y → just ((C ⊕+ just x) y)} {λ x y → just ((C ⊕+ just x) y)} refl {p'} {(C ⊕+ nothing) p'} (sym ax2) {subst (λ x → Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) x)) p'' ax2} {p''} (stripsubst (λ z → Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) z)) p'' ax2)))) 

    ax5' {s} (just p) nothing nothing = sym (trans (cong (C ⊕ just p) (ax4' (subst Pos' nothing (ax1 {s} {just p} {nothing})))) (cong (C ⊕ just p) (stripsubst Pos' nothing (ax1 {s} {just p} {nothing}))))

    ax5' {s} (just p) nothing (just p'') = sym (cong' {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} {(C ⊕ nothing)(subst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) (just p'') (ax1 {s} {just p} {nothing}))} {just p''} (trans (ax4' ((subst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) (just p'') (ax1 {s} {just p} {nothing})))) (stripsubst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) (just p'') (ax1 {s} {just p} {nothing}))) {λ x → Maybe (Pos+ (C₁ (C₂ C)) s)} {λ x → Maybe (Pos+ (C₁ (C₂ C)) s)} refl {C ⊕ just p} {C ⊕ just p} refl) 

    ax5' {s} (just p) (just p') nothing = sym (cong' {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} {(C ⊕ just p') (subst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) nothing (ax1 {s} {just p} {just p'}))} {just p'} (cong' {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ (C₁ (C₂ C) ↓+ s) p) p'))} {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ (C₁ (C₂ C) ↓+ s) p) p'))} {subst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) nothing (ax1 {s} {just p} {just p'})} {nothing} (trans (stripsubst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) nothing (ax1 {s} {just p} {just p'})) (icong' ax3 refl {λ {s'} → nothing {Pos+ (C₁ (C₂ C)) s'}} {λ {s'} → nothing {Pos+ (C₁ (C₂ C)) s'}} refl)) {λ x → Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} {λ x → Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ s) p))} refl {C ⊕ just p'} {C ⊕ just p'} refl) {λ x → Maybe (Pos+ (C₁ (C₂ C)) s)} {λ x → Maybe (Pos+ (C₁ (C₂ C)) s)} refl {C ⊕ just p} {C ⊕ just p} refl )

    ax5' {s} (just p) (just p') (just p'') = sym (trans (cong (C ⊕ just p) ax5'-lem1) (cong just ax6)) where
      ax5'-lem1 : (C ⊕ just p') (subst (Pos (C₂ C)) (just p'') (ax1 {s} {just p} {just p'})) == just ((C ⊕+ just p') ((subst (Pos+ (C₁ (C₂ C))) p'' (ax1 {s} {just p} {just p'}))))
      ax5'-lem1 = cong' {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ (C₁ (C₂ C) ↓+ s) p) p'))} {Maybe (Pos+ (C₁ (C₂ C)) ((C₁ (C₂ C) ↓+ (C₁ (C₂ C) ↓+ s) p) p'))} {subst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) (just p'') (ax1 {s} {just p} {just p'})} {just (subst (Pos+ (C₁ (C₂ C))) p'' (ax1 {s} {just p} {just p'}))} (trans (stripsubst (λ x → Maybe (Pos+ (C₁ (C₂ C)) x)) (just p'') (ax1 {s} {just p} {just p'})) (cong' (sym (stripsubst (Pos+ (C₁ (C₂ C))) p'' (ax1 {s} {just p} {just p'}))) (ext' (λ x → cong (λ x' → Maybe (Pos+ (C₁ (C₂ C)) x')) ax5)) {just} {just} (icong' {Shape (C₁ (C₂ C))} {Shape (C₁ (C₂ C))} {(C₁ (C₂ C) ↓+ s) ((C ⊕+ just p) p')} {(C₁ (C₂ C) ↓+ (C₁ (C₂ C) ↓+ s) p) p'} ax5 refl {λ {x} → just {Pos+ (C₁ (C₂ C)) x}} {λ {x} → just {Pos+ (C₁ (C₂ C)) x}} refl))) refl {C ⊕ just p'} {C ⊕ just p'} refl

  infixl 50 _↓'_
  infixl 60 _⊕'_
