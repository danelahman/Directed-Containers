{-# OPTIONS --type-in-type #-}

open import Utils
open import Containers using (Container)

module DContainers  where

record DContainer : Set where
  constructor _◁_
  field Shape : Set
        Pos : Shape → Set
        _↓_ : (s : Shape) → Pos s → Shape 
        o : {s : Shape} → Pos s
        _⊕_ : {s : Shape} → (p : Pos s) → Pos (s ↓ p) → Pos s
        ax1 : {s : Shape} → s ↓ o == s
        ax2 : {s : Shape} → {p : Pos s} → {p' : Pos (s ↓ p)} → s ↓ p ⊕ p' == s ↓ p ↓ p'
        ax3 : {s : Shape} → (p : Pos s) → p ⊕ o == p
        ax4 : {s : Shape} → (p : Pos (s ↓ o)) → o ⊕ p == p
        ax5 : {s : Shape} → (p : Pos s) → (p' : Pos (s ↓ p)) → (p'' : Pos (s ↓ p ⊕ p')) → p ⊕ p' ⊕ p'' == p ⊕ (p' ⊕ subst Pos p'' ax2)

  infixl 50 _↓_
  infixl 60 _⊕_

⌈_⌉ : DContainer → Container
⌈ _◁_ Shape Pos _↓_ o _⊕_ ax1 ax2 ax3 ax4 ax5 ⌉ = Container._◁_ Shape Pos

open DContainer

dcon-eq : (C C' : DContainer) → Shape C == Shape C' → Pos C == Pos C' → _↓_ C == _↓_ C' → (λ {s} → o C {s}) == (λ {s} → o C' {s}) → (λ {s} → _⊕_ C {s}) == (λ {s} → _⊕_ C' {s}) → C == C'
dcon-eq C C' p p' p'' p''' p'''' = cong10 
  {Set} 
  {λ Shape → (Shape → Set)} 
  {λ Shape Pos → ((s : Shape) → Pos s → Shape)} 
  {λ Shape Pos _ → ({s : Shape} → Pos s)} 
  {λ Shape Pos _↓_ _ → ({s : Shape} → (p : Pos s) → Pos (s ↓ p) → Pos s)} 
  {λ Shape Pos _↓_ o _⊕_ → ({s : Shape} → (s ↓ o) == s)} 
  {λ Shape Pos _↓_ o _⊕_ ax1 → ({s : Shape} → {p : Pos s} → {p' : Pos (s ↓ p)} → (s ↓ (p ⊕ p')) == ((s ↓ p) ↓ p'))} 
  {λ Shape Pos _↓_ o _⊕_ ax1 ax2 → ({s : Shape} → (p : Pos s) → (p ⊕ o) == p)} 
  {λ Shape Pos _↓_ o _⊕_ ax1 ax2 ax3 → ({s : Shape} → (p : Pos (s ↓ o)) → (o ⊕ p) == p)} 
  {λ Shape Pos _↓_ o _⊕_ ax1 ax2 ax3 ax4 → ({s : Shape} → (p : Pos s) → (p' : Pos (s ↓ p)) → (p'' : Pos (s ↓ (p ⊕ p'))) → ((p ⊕ p') ⊕ p'') == (p ⊕ (p' ⊕ subst Pos p'' ax2)))} 
  {λ _ _ _ _ _ _ _ _ _ _ → DContainer} 
  (λ Shape Pos ↓ o ⊕ ax1 ax2 ax3 ax4 ax5 → record {Shape = Shape ; Pos = Pos ; _↓_ = ↓ ; o = o ; _⊕_ = ⊕ ; ax1 = ax1 ; ax2 = ax2 ; ax3 = ax3 ; ax4 = ax4 ; ax5 = ax5}) 
  p 
  p' 
  p'' 
  p''' 
  p'''' 
  (iext' (λ {s} {s'} q → fixtypes (cong' (icong' q p' p''') (ext' (λ _ → p)) (cong' q (ext' (λ x → cong2 (λ x' y → x' → y) (cong' x (ext' (λ x' → refl)) p') p)) p'')) q))
  ax2lem
  (iext' (λ x → ext' (λ x' → fixtypes (cong' (icong' (cong' x' (ext' λ _ → p) (cong' x (ext' (λ x0 → cong2 (λ x1 y → x1 → y) (cong' x0 (ext' λ _ → refl) p') p)) p'')) p' p''') (ext' λ _ → cong' x (ext' λ _ → refl) p') (cong' x' (ext' (λ x0 → cong2 (λ x1 y → x1 → y) (cong' (cong' x0 (ext' λ _ → p) (cong' x (ext' (λ y → cong2 (λ x1 y' → x1 → y') (cong' y (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p') (cong' x (ext' λ _ → refl) p'))) (icong' x (ext' (λ x0 → cong3 (λ x1 (y : _ → Set) z → (x2 : x1) → y x2 → z) (cong' x0 (ext' λ _ → refl) p') (ext' (λ x1 → cong' (cong' x1 (ext' λ _ → p) (cong' x0 (ext' (λ x2 → cong2 (λ x3 y → x3 → y) (cong' x2 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p')) (cong' x0 (ext' λ _ → refl) p' ))) p''''))  ) x')))
  (iext' (λ x → ext' (λ {a} {a'} x' → fixtypesX (cong' x' (ext' (λ x0 → cong' x (ext' λ _ → refl) p')) (cong' (icong' x (ext' (λ x0 → cong' x0 (ext' λ _ → refl) p')) p''') (ext' (λ x0 → cong2 (λ x1 y → x1 → y) (cong' (cong' x0 (ext' λ _ → p) (cong' x (ext' (λ x1 → cong2 (λ x2 y → x2 → y) (cong' x1 (ext' λ _ → refl) p') p)) p'')) (ext' (λ _ → refl)) p') (cong' x (ext' (λ _ → refl)) p'))) (icong' x (ext' (λ x0 → cong3 (λ x1 (y : _ → Set) z → (x2 : x1) → y x2 → z) (cong' x0 (ext' (λ _ → refl)) p') (ext' (λ x1 → cong' (cong' x1 (ext' λ _ → p) (cong' x0 (ext' (λ x2 → cong2 (λ x y → x → y) (cong' x2 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p')) (cong' x0 (ext' λ _ → refl) p'))) p''''))) x'))) 
  (iext' (λ x → ext' (λ x' → ext' (λ x0 → ext' (λ {a4}{a5} x1 → fixtypes (cong' x1 (ext' λ _ → cong' x (ext' λ _ → refl) p') (cong' (cong' x0 (ext' λ _ → cong' x (ext' λ _ → refl) p') (cong' x' (ext' (λ x2 → cong2 (λ x3 y → x3 → y) (cong' (cong' x2 (ext' λ _ → p) (cong' x (ext' (λ x3 → cong2 (λ x y → x → y) (cong' x3 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p') (cong' x (ext' λ _ → refl) p'))) (icong' x (ext' (λ x2 → cong3 (λ x3 (y : _ → Set) z → (x4 : x3) → y x4 → z) (cong' x2 (ext' λ _ → refl) p') (ext' (λ x3 → cong' (cong' x3 (ext' λ _ → p) (cong' x2 (ext' (λ x4 → cong2 (λ x y → x → y) (cong' x4 (ext' λ _ → refl) p')  p)) p'')) (ext' λ _ → refl) p')) (cong' x2 (ext' λ _ → refl) p'))) p''''))) (ext' (λ x2 → cong2 (λ x3 y → x3 → y) (cong' (cong' x2 (ext' λ _ → p) (cong' x (ext' (λ x3 → cong2 (λ x4 y → x4 → y) (cong' x3 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p') (cong' x (ext' λ _ → refl) p'))) (icong' x (ext' (λ x2 → cong3 (λ x3 (y : _ → Set) z → (x4 : x3) → y x4 → z) (cong' x2 (ext' λ _ → refl) p') (ext' (λ x3 → cong' (cong' x3 (ext' λ _ → p) (cong' x2 (ext' λ x4 → cong2 (λ x y → x → y) (cong' x4 (ext' λ _ → refl) p') p  ) p'')) (ext' λ _ → refl) p')) (cong' x2 (ext' λ _ → refl) p' ))) p''''))) (cong' (cong' (trans (stripsubst (Pos C) a4 (ax2 C)) (trans x1 (sym (stripsubst (Pos C') a5 (ax2 C'))))) (ext' (λ x2 → cong' (cong' x' (ext' λ _ → p) (cong' x (ext' (λ x3 → cong2 (λ x4 y → x4 → y) (cong' x3 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p')) (cong' x0 (ext' (λ x2 → cong2 (λ x3 y → x3 → y) (cong' (cong' x2 (ext' λ _ → p) (cong' (cong' x' (ext' λ _ → p) (cong' x (ext' (λ x3 → cong2 (λ x y → x → y) (cong' x3 (ext' λ _ → refl) p') p)) p'')) (ext' (λ x3 → cong2 (λ x y → x → y) (cong' x3 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p') (cong' (cong' x' (ext' λ _ → p) (cong' x (ext' (λ x3 → cong2 (λ x y → x → y) (cong' x3 (ext' λ _ → refl) p') p )) p'')) (ext' λ _ → refl) p'))) (icong' (cong' x' (ext' λ _ → p) (cong' x (ext' (λ x2 → cong2 (λ x y → x → y) (cong' x2 (ext' λ _ → refl) p') p )) p'')) (ext' (λ x2 → cong3 (λ x3 (y : _ → Set) z → (x4 : x3) → y x4 → z) (cong' x2 (ext' λ _ → refl) p') (ext' (λ x3 → cong' (cong' x3 (ext' λ _ → p) (cong' x2 (ext' (λ x4 → cong2 (λ x y → x → y) (cong' x4 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p')) (cong' x2 (ext' λ _ → refl) p'))) p''''))) (ext' λ _ → cong' x (ext' λ _ → refl) p') (cong' x' (ext' (λ x2 → cong2 (λ x3 y → x3 → y) (cong' (cong' x2 (ext' λ _ → p) (cong' x (ext' (λ x3 → cong2 (λ x y → x → y) (cong' x3 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p') (cong' x (ext' λ _ → refl) p'))) (icong' x (ext' (λ x2 → cong3 (λ x3 (y : _ → Set) z → (x4 : x3) → y x4 → z) (cong' x2 (ext' λ _ → refl) p') (ext' (λ x3 → cong' (cong' x3 (ext' λ _ → p) (cong' x2 (ext' (λ x4 → cong2 (λ x y → x → y) (cong' x4 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p')) (cong' x2 (ext' λ _ → refl) p'))) p''''))  ))))))
  where
  ax2lem = (iext' (λ x → iext' (λ x' → iext' (λ x0 → fixtypes (cong' (cong' x0 (ext' (λ _ → cong' x (ext' λ _ → refl) p')) (cong' x' (ext' λ{z}{z'} y → cong2 (λ x y → x → y) (cong' (cong' y (ext' λ _ → p) (cong' x (ext' (λ y' → cong2 (λ x y → x → y) (cong' y' (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p') (cong' x (ext' λ _ → refl) p')) (icong' x (ext' (λ y → cong3 (λ x1 (y' : _ → Set) z → (x2 : x1) → y' x2 → z) (cong' y (ext' λ _ → refl) p') (ext' (λ x1 → cong' (cong' x1 (ext' λ _ → p) (cong' y (ext' (λ x2 → cong2 (λ x y → x → y) (cong' x2 (ext' λ _ → refl) p') p)) p'')) (ext' λ _ → refl) p')) (cong' y (ext' λ _ → refl) p') ) ) p''''))) (ext' λ _ → p) (cong' x (ext' λ y → cong2 (λ x1 y' → x1 → y') (cong' y (ext' λ _ → refl) p') p) p'')) (cong' x0 (ext' λ _ → p) (cong' (cong' x' (ext' λ _ → p) (cong' x (ext' (λ y → cong2 (λ x y → x → y) (cong' y (ext' λ _ → refl) p') p)) p'')) (ext' (λ y → cong2 (λ x y → x → y) (cong' y (ext' λ _ → refl) p') p)) p'') ))))) 

Id-DCon : DContainer
Id-DCon = _◁_ ⊤ (λ _ → ⊤) (λ s p → tt) (λ {s} → tt) (λ {s} p p' → tt) ax1' (λ {s} {p} {p'} → refl) ax3' ax4' (λ {s} p p' p'' → refl) where
  ax1' : {s : ⊤} → tt == s
  ax1' {tt} = refl
  ax3' : {s : ⊤} (p : ⊤) → tt == p
  ax3' tt = refl
  ax4' : {s : ⊤} (p : ⊤) → tt == p
  ax4' tt = refl

record _⇒_ (C C' : DContainer) : Set where
  constructor _◁_
  field sf : Shape C → Shape C'
        pf : {s : Shape C} → Pos C' (sf s) → Pos C s
        ax6 : {s : Shape C} → {p : Pos C' (sf s)} → _↓_ C' (sf s) p == sf (_↓_ C s (pf {s} p))
        ax7 : {s : Shape C} → pf {s} (o C') == o C {s}
        ax8 : {s : Shape C} → (p : Pos C' (sf s)) → (p' : Pos C' (_↓_ C' (sf s) p)) → pf {s} (_⊕_ C' p p') == _⊕_ C (pf {s} p) (pf (subst (Pos C') p' ax6))

open _⇒_


⇒-id : {C : DContainer} → C ⇒ C
⇒-id {_◁_ s p _↓_ o _⊕_ ax1 ax2 ax3 ax4 ax5} = ((λ s → s) ◁ (λ p → p)) (λ {s p} → refl) (λ {s} → refl) (λ {s} p p' → refl)


_∘_ : {C D E : DContainer} → (f : C ⇒ D) → (g : D ⇒ E) → C ⇒ E
_∘_ {_◁_ Shape₀ Pos₀ _↓₀_ o₀ _⊕₀_ ax1₀ ax2₀ ax3₀ ax4₀ ax5₀} {_◁_ Shape₁ Pos₁ _↓₁_ o₁ _⊕₁_ ax1₁ ax2₁ ax3₁ ax4₁ ax5₁} {_◁_ Shape₂ Pos₂ _↓₂_ o₂ _⊕₂_ ax1₂ ax2₂ ax3₂ ax4₂ ax5₂} (_◁_ sf₀ pf₀ ax6₀ ax7₀ ax8₀) (_◁_ sf₁ pf₁ ax6₁ ax7₁ ax8₁) = _◁_ (λ s → sf₁ (sf₀ s)) (λ p → pf₀ (pf₁ p)) ax6₂ ax7₂ ax8₂ where
               ax6₂ : {s : Shape₀} → {p : Pos₂ (sf₁ (sf₀ s))} → (sf₁ (sf₀ s) ↓₂ p) == sf₁ (sf₀ (s ↓₀ pf₀ (pf₁ p)))
               ax6₂ {s} {p} = trans (ax6₁ {sf₀ s} {p}) (cong sf₁ (ax6₀ {s} {pf₁ p})) 
               ax7₂ : {s : Shape₀} → pf₀ {s} (pf₁ o₂) == o₀ {s}
               ax7₂ {s} = trans (cong pf₀ (ax7₁ {sf₀ s})) (ax7₀ {s})
               ax8₂ : {s : Shape₀} → (p : Pos₂ (sf₁ (sf₀ s))) → (p' : Pos₂ (sf₁ (sf₀ s) ↓₂ p)) → pf₀ (pf₁ (p ⊕₂ p')) == (pf₀ (pf₁ p) ⊕₀ pf₀ (pf₁ (subst (λ p → Pos₂ p) p' (trans ax6₁ (cong sf₁ ax6₀)))))
               ax8₂ {s} p p' = trans (trans (cong pf₀ (ax8₁ _ _)) (trans (ax8₀ (pf₁ p) (pf₁ (subst Pos₂ p' ax6₁))) (cong (λ t → pf₀ (pf₁ p) ⊕₀ pf₀ t) (substcong2 Pos₁ Pos₂ sf₁ pf₁ (subst Pos₂ p' ax6₁) ax6₀)))) (cong (λ t → pf₀ (pf₁ p) ⊕₀ pf₀ (pf₁ t) ) (substtrans Pos₂ p' ax6₁ (cong sf₁ ax6₀)))


⇒-eq : {C D : DContainer} →  (f g : C ⇒ D) → sf f == sf g → (∀ s → pf f {s} == pf g {s}) → f == g
⇒-eq {C} {D} f g p q = cong5 
  {Shape C → Shape D}
  {C ⇒ D}
  {λ sf → {s : Shape C} → Pos D (sf s) → Pos C s}
  {λ sf pf → {s : Shape C} → {p : Pos D (sf s)} → _↓_ D (sf s) p == sf (_↓_ C s (pf {s} p))}
  {λ sf pf → {s : Shape C} → pf {s} (o D) == o C {s}}
  {λ sf pf ax6 → {s : Shape C} → (p : Pos D (sf s)) → (p' : Pos D (_↓_ D (sf s) p)) → pf {s} (_⊕_ D p p') == _⊕_ C (pf {s} p) (pf (subst (Pos D) p' (ax6 )))}
  (λ w x y z z' -> record {sf = w ; pf = x ; ax6 = y ; ax7 = z ; ax8 = z' })
  p
  (iext q) 
  eq1 
  (iext (λ a → fixtypes (cong' (icong (λ {x} → o D {x}) (cong' refl (ext (λ _ → refl)) p)) (ext' (λ _ → refl)) (q a) ) refl)) 
  (iext (λ a → ext' (λ {a0}{a1} p' → ext' (λ {a0'}{a1'} p'' → fixtypes (cong' (cong' p'' (ext' (λ _ → cong (Pos D) (cong' refl refl p))) (cong' p' (ext' (λ x → cong2 (λ x y → (Pos D ((D ↓ x) y) → Pos D (x))) (cong' refl refl p) x )) (icong (λ {x} → _⊕_ D {x}) (cong' refl refl p)))) (ext' (λ _ → refl)) (q a)) (cong' ((cong' (cong4 (λ y p z q → subst (Pos D) {y} p {z} q) (cong' p' (ext' (λ _ → refl)) (cong' (cong' (refl {a = a}) (ext' (λ _ → refl)) p) (ext (λ a' → refl)) (refl {a = _↓_ D})) ) p'' (cong' (cong (C ↓ a) (cong' p' (ext' (λ _ → refl)) (q a))) (ext (λ _ → refl)) p) (icong' p' (ext' (λ {b} {b'} x → cong2 (λ s t → _==_ {Shape D} s {Shape D} t) (cong' x (ext' (λ _ → refl)) (cong' (cong' (refl {a = a}) (ext' (λ _ → refl)) p) (ext' (λ x' → cong2 (λ x y → x → y) (cong (Pos D) x') refl)) (refl {a = _↓_ D}))) (cong' (cong' (cong' x (ext' (λ _ → refl)) (q a)) (ext' (λ _ → refl)) (refl {a = C ↓ a})) (ext' (λ _ → refl)) p))) (icong' (refl {a = a}) (ext (λ a' → lem (cong (Pos D) (cong' (refl {a = a'}) (ext (λ _ → refl)) p)) (ext' (λ x → cong2 (λ x y → _==_ {Shape D} x {Shape D} y) (cong' x (ext' (λ _ → refl)) (cong' (cong' (refl {a = a'}) refl p) (ext (λ _ → refl)) (refl {a = _↓_ D}))) (cong' (cong (C ↓ a') (cong' x (ext' (λ _ → refl)) (q a'))) (ext (λ a2 → refl)) p ))))) eq1)) ) {λ _ → Pos C ((C ↓ a) (pf f a0))}{λ _ → Pos C ((C ↓ a) (pf g a1))} ((ext' (λ a' → cong (Pos C) (cong (C ↓ a) (cong' p' (ext' (λ x → refl)) (q a)))))) (pflem {C} {D} {f} {g} q (cong' (cong' p' (ext' (λ _ → refl)) (q a)) (ext' (λ _ → refl)) (refl {a = C ↓ a}))))) (ext' (λ _ → refl)) (dcong (_⊕_ C) (cong' p' (ext' (λ _ → refl)) (q a))))))))
  where
  eq1 = (iext (λ s → iext3 (λ p' → fixtypes (cong' p' (ext' λ _ → refl) (dcong (λ x → (D ↓ x s)) p)) (cong' (cong' (cong' p' (ext' (λ _ → refl)) (q s)) (ext' (λ _ → refl)) (refl {a = C ↓ s})) (ext' (λ _ → refl)) p))))
  lem : ∀ {S S'} {P : S → Set} {P' : S' → Set} → (S == S') → (P == P') → ({x : S} → P x) == ({x : S'} → P' x)
  lem refl refl = refl
  pflem : {C D : DContainer}{f g : C ⇒ D} → (∀ a → pf f {a} == pf g {a}) → ∀{a a'}(p : a == a') → pf f {a} == pf g {a'}
  pflem p refl = p _

abstract
  ∘rid : {C D : DContainer} → (f : C ⇒ D) → f == (f ∘ ⇒-id)
  ∘rid f = ⇒-eq _ _ refl (λ _ → refl)
  
  ∘lid : {C D : DContainer} → (f : C ⇒ D) → f == (⇒-id ∘ f)
  ∘lid f = ⇒-eq _ _ refl (λ _ → refl)    

  ∘assoc : {C D E F : DContainer} → (f : C ⇒ D) → (g : D ⇒ E) → (h : E ⇒ F) → f ∘ g ∘ h == f ∘ (g ∘ h)
  ∘assoc f g h = ⇒-eq _ _ refl (λ s → refl)


infixl 60 _∘_









