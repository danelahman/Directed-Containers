{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers renaming (⌜_⌝ to ⌜_⌝' ; _⇒_ to _⇒'_ ; ⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁')
open import DContainers renaming (⌈_⌉ to ⌈_⌉')
open import DContainerExt
open import Comonads
open import Functors
open import Comonad2DContainer

open import Comonad2DContainer
open import ComonadMorph2DContainerMorph

module InterpretQuoteLem1 where

open Container
open DContainer renaming (Shape to Shape' ; Pos to Pos')
open Containers._⇒_
open Functor
open Comonad
open _⇛_
open _⇨_

⟦⌈⌉⟧₀-lem : (C : Container) → (CM : Comonad) → (p : Fun CM == ⟦ C ⟧₀') → ⟦ ⌈ CM , p ⌉ ⟧₀ == CM
⟦⌈⌉⟧₀-lem (Shape ◁ Pos) (CM .(Functor⋆ (λ X → ∃ Shape (λ s → Pos s → X)) (λ f r → ∃.fst∃ r , (λ x → f (∃.snd∃ r x))) refl refl) counit comult lunit-ax runit-ax assoc-ax) refl = 
  comonad-eq 
    ⟦ ⌈ (CM (Functor⋆ (λ X → ∃ Shape (λ s → Pos s → X)) (λ f r → ∃.fst∃ r , (λ x → f (∃.snd∃ r x))) refl refl) counit comult lunit-ax runit-ax assoc-ax) , refl ⌉ ⟧₀
    (CM (Functor⋆ (λ X → ∃ Shape (λ s → Pos s → X)) (λ f r → ∃.fst∃ r , (λ x → f (∃.snd∃ r x))) refl refl) counit comult lunit-ax runit-ax assoc-ax) 
    (functor-eq 
      (Fun (⟦ ⌈ (CM (Functor⋆ (λ X → ∃ Shape (λ s → Pos s → X)) (λ f r → ∃.fst∃ r , (λ x → f (∃.snd∃ r x))) refl refl) counit comult lunit-ax runit-ax assoc-ax) , refl ⌉ ⟧₀)) 
      (Fun (CM (Functor⋆ (λ X → ∃ Shape (λ s → Pos s → X)) (λ f r → ∃.fst∃ r , (λ x → f (∃.snd∃ r x))) refl refl) counit comult lunit-ax runit-ax assoc-ax)) 
      refl 
      refl) 
  (nat-eq _ _ (ext (λ s → cong' refl refl (nat counit (∃.snd∃ s))))) 
  (nat-eq _ _ (ext (λ s → 
    trans 
      (∃-eq 
        refl 
        (sym (c2dc.comult'-ax1 counit comult lunit-ax runit-ax assoc-ax)) 
        (ext' (λ {p} {p'} x → 
          ∃-eq 
            refl 
            (cong 
              (λ x → ∃.fst∃ (∃.snd∃ (tr comult (∃.fst∃ s , (λ x' → x'))) x)) 
              (trans (stripsubst (λ z → Pos z) p (sym (c2dc.comult'-ax1 counit comult lunit-ax runit-ax assoc-ax))) x)) 
            (ext' (λ {p''} {p'''} x' → 
              cong2 
                (λ x y → ∃.snd∃ s (∃.snd∃ (∃.snd∃ (tr comult (∃.fst∃ s , (λ x0 → x0))) x) y)) 
                (trans (stripsubst (λ z → Pos z) p (sym (c2dc.comult'-ax1 counit comult lunit-ax runit-ax assoc-ax))) x) 
                x'))))) 
      (cong' refl refl (nat comult (∃.snd∃ s)))))) 
