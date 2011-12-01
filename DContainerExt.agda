{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers renaming (_∘_ to _∘'_)
open import Functors
open import Comonads

module DContainerExt  where

open Functor
open _⇛_
open Comonad
open _⇨_

⟦_⟧₀ : DContainer → Comonad
⟦ _◁_ S P _↓_ o _⊕_ ax1 ax2 ax3 ax4 ax5 ⟧₀ = CM Fun' (record {tr = counit' ; nat = counit-nat'}) (record {tr = comult' ; nat = comult-nat'}) (nat-eq _ _ lunit-ax') (nat-eq _ _ runit-ax') (nat-eq _ _ assoc-ax') where
  Fun' : Functor
  Fun' = record {omap = λ X → ∃ S (λ s → P s → X) ; fmap = λ f p → ∃.fst∃ p , (f · ∃.snd∃ p) ; id-ax = refl ; comp-ax = refl}

  counit' : {A : Set} → ∃ S (λ s → P s → A) → A
  counit' (s , f) = f (o {s})

  comult' : {A : Set} → ∃ S (λ s → P s → A) → ∃ S (λ s → P s → ∃ S (λ s' → P s' → A))
  comult' (s , f) = s , (λ p → (s ↓ p , λ p' → f (p ⊕ p')))

  lunit-ax' : {A : Set} → counit' · comult' {A} == identity {omap Fun' A}
  lunit-ax' {A} = trans f f' where
    f : (λ s → ∃.fst∃ s ↓ o , λ p' → ∃.snd∃ s (o ⊕ p')) == λ s → ∃.fst∃ s , λ p → ∃.snd∃ s p
    f =  ext (λ s → cong2 {S} {λ s' → P s' → A} {λ x y → ∃ S (λ s → (P s → A)) } _,_ ax1 (ext' (λ x → cong (∃.snd∃ s) (trans (ax4 _) x))))
    f' : (λ s → ∃.fst∃ s , λ p → ∃.snd∃ s p) == λ s → s
    f' = ext (λ s → refl)

  runit-ax' : {A : Set} → fmap Fun' counit' · comult' {A} == identity {omap Fun' A}
  runit-ax' {A} = trans f f' where
    f : (λ s → ∃.fst∃ s , counit' · λ p → ∃.fst∃ s ↓ p , λ p' → ∃.snd∃ s (p ⊕ p')) == λ s → ∃.fst∃ s , λ p → ∃.snd∃ s p
    f = ext (λ s → cong (λ p → ∃.fst∃ s , p) (ext (λ a → cong (∃.snd∃ s) (ax3 a))))
    f' : (λ s → ∃.fst∃ s , λ p → ∃.snd∃ s p) == λ s → s
    f' = ext (λ x → refl)

  assoc-ax' : {A : Set} → comult' · comult' {A} == fmap Fun' comult' · comult' {A}
  assoc-ax' {A} = ext (λ s → cong (λ p → ∃.fst∃ s , p) (ext (λ a → cong (λ p → (∃.fst∃ s ↓ a) , p) (ext (λ a' → cong2 {S} {_} {λ _ _ → ∃ S (λ s' → P s' → A)} _,_ ax2 (ext' (λ x → dcong (∃.snd∃ s) (trans (ax5 _ _ _) (cong (λ x → a ⊕ (a' ⊕ x)) (trans (stripsubst P _ ax2) x))))))))))

  counit-nat' : {A B : Set} (f : A → B) → counit' · fmap Fun' f == f · counit'
  counit-nat' f = refl

  comult-nat' :  {A B : Set} (f : A → B) → comult' · fmap Fun' f == fmap Fun' (fmap Fun' f) · comult'
  comult-nat' f = refl


⟦_⟧₁ : {C C' : DContainer} → C ⇒ C' → ⟦ C ⟧₀ ⇨ ⟦ C' ⟧₀
⟦_⟧₁ {_◁_ S P _↓_ o _⊕_ ax1 ax2 ax3 ax4 ax5} {_◁_ S' P' _↓'_ o' _⊕'_ ax1' ax2' ax3' ax4' ax5'} (_◁_ sf pf ax6 ax7 ax8) = record { tr' = record { tr = tr'' ; nat = nat''} ; cu = nat-eq _ _ (λ {X} → cu' {X}) ; cm = nat-eq _ _ (sym (cm' {_})) } where
  tr'' : {X : Set} → ∃ S (λ s → P s → X) → ∃ S' (λ s → P' s → X)
  tr'' (s , f) = (sf s) , (f · pf)
  nat'' : {X Y : Set} (h : X → Y) → fmap (Fun ⟦ _◁_ S' P' _↓'_ o' _⊕'_ ax1' ax2' ax3' ax4' ax5' ⟧₀) h · tr'' == tr'' · fmap (Fun ⟦ _◁_ S P _↓_ o _⊕_ ax1 ax2 ax3 ax4 ax5 ⟧₀) h
  nat'' h = refl
  cu' : {X : Set} → tr (counit ⟦ _◁_ S' P' _↓'_ o' _⊕'_ ax1' ax2' ax3' ax4' ax5' ⟧₀) · tr'' == tr (counit ⟦ _◁_ S P _↓_ o _⊕_ ax1 ax2 ax3 ax4 ax5 ⟧₀)
  cu' = ext (λ s → cong (∃.snd∃ s) ax7)
  cm' : {X : Set} → fmap (Fun ⟦ _◁_ S' P' _↓'_ o' _⊕'_ ax1' ax2' ax3' ax4' ax5' ⟧₀) tr'' · tr'' · tr (comult ⟦ _◁_ S P _↓_ o _⊕_ ax1 ax2 ax3 ax4 ax5 ⟧₀) == tr (comult ⟦ _◁_ S' P' _↓'_ o' _⊕'_ ax1' ax2' ax3' ax4' ax5' ⟧₀) · tr''
  cm' {X} = ext' (λ {b} {b'} x → cong2 {_} {_} {λ _ _ → ∃ S' (λ s → P' s → ∃ S' (λ s' → P' s' → X))} _,_ (cong (λ x → sf (∃.fst∃ x)) x) (ext' (λ {a} {a'} x' → cong2 {_} {_} {λ _ _ → ∃ S' (λ s' → P' s' → X)} _,_ (trans (sym ax6) (cong2 (λ y y' → (sf (∃.fst∃ y) ↓' y')) x x')) (ext' (λ {a0} {a1} x'' → cong2 {∃ S (λ s → P s → X)} {λ x → P (∃.fst∃ x)} {λ _ _ → X} (λ x y → ∃.snd∃ x y) x (trans (((cong2''' (cong (λ y → P ( ∃.fst∃ y)) x) (ext' (λ x0 → cong P (cong2 (λ x → _↓_ (∃.fst∃ x)) x x0))) {λ _ _ → P (∃.fst∃ {S} {λ x1 → P x1 → X} b)} {λ _ _ → P (∃.fst∃ {S} {λ x1 → P x1 → X} b')} (ext' (λ x0 → ext' (λ x1 → cong (λ y → P (∃.fst∃ y)) x))) {_⊕_ {∃.fst∃ {S} {λ s → P s → X} b}} {_⊕_ {∃.fst∃ {S} {λ x1 → P x1 → X} b'}} (cong' (cong ∃.fst∃ x) refl {λ x → _⊕_ {x}} {λ x → _⊕_ {x}} refl) ((cong' x' (ext' (λ x0 → cong (λ y → P (∃.fst∃ y)) x)){pf {∃.fst∃ {S} {λ s → P s → X} b}}{pf {∃.fst∃ {S} {λ x1 → P x1 → X} b'}} (cong' (cong ∃.fst∃ x) refl {λ x → pf {x}} {λ x → pf {x}} refl))) (cong' (trans x'' (sym (stripsubst P' _ ax6))) (ext' (λ x0 → cong2 (λ x y → P (∃.fst∃ x ↓ pf y)) x x')) {pf {∃.fst∃ {S} {λ s → P s → X} b ↓ pf {∃.fst∃ {S} {λ s → P s → X} b} a}}{pf {∃.fst∃ {S} {λ x1 → P x1 → X} b' ↓ pf {∃.fst∃ {S} {λ x1 → P x1 → X} b'} a'}} (cong' (cong2 (λ x y → ∃.fst∃ x ↓ pf y) x x') refl {λ x → pf {x}} {λ x → pf {x}} refl))))) (sym (ax8 _ _))))))))

⟦⟧₁-id-eq : {C : DContainer} → ⟦ ⇒-id {C} ⟧₁ == ⇨-id {⟦ C ⟧₀}
⟦⟧₁-id-eq {C} = comonad-morph-eq _ _ (λ X → refl)

∘-dist : {C C' C'' : DContainer} → (f : C ⇒ C') → (g : C' ⇒ C'') → ⟦ f ∘' g ⟧₁ == (⟦ f ⟧₁ c∘ ⟦ g ⟧₁)
∘-dist {C} f g = comonad-morph-eq _ _ (λ X → ext (λ a → refl))
