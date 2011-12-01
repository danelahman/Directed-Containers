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
open import FullyFaithfulLem1
open import InterpretQuoteLem1

module FullyFaithfulLem2 where

open Container
open DContainer renaming (Shape to Shape' ; Pos to Pos')
open Functor
open Comonad
open _⇛_
open _⇨_
open DContainers._⇒_

comonad-morph-eq' : {C C' C'' C''' : Comonad} → (f : C ⇨ C')(g : C'' ⇨ C''') → C == C'' → C' == C'''  → (∀ X → tr (tr' f) {X} == tr (tr' g) {X}) → f == g
comonad-morph-eq' f g refl refl = comonad-morph-eq f g

fully-faithful-lem2 : (C₀ C₁ : Container) → (CM₀ CM₁ : Comonad) → (τ : CM₀ ⇨ CM₁) → (p : Fun CM₀ == ⟦ C₀ ⟧₀') → (q : Fun CM₁ == ⟦ C₁ ⟧₀') → ⟦ ⌜ CM₀ , CM₁ , p , q , τ ⌝ ⟧₁ == τ

fully-faithful-lem2 (Shape₀ ◁ Pos₀) (Shape₁ ◁ Pos₁) (CM .(Functor⋆ (λ X → ∃ Shape₀ (λ s → Pos₀ s → X)) (λ f r' → ∃.fst∃ r' , (λ x → f (∃.snd∃ r' x))) refl refl) counit₀ comult₀ lunit-ax₀ runit-ax₀ assoc-ax₀) (CM .(Functor⋆ (λ X → ∃ Shape₁ (λ s → Pos₁ s → X)) (λ f r' → ∃.fst∃ r' , (λ x → f (∃.snd∃ r' x))) refl refl) counit₁ comult₁ lunit-ax₁ runit-ax₁ assoc-ax₁) τ refl refl =
   comonad-morph-eq' 
     _
     _ 
     (⟦⌈⌉⟧₀-lem (Shape₀ ◁ Pos₀) (CM (Functor⋆ (λ X → ∃ Shape₀ (λ s → Pos₀ s → X)) (λ f r' → ∃.fst∃ r' , (λ x → f (∃.snd∃ r' x))) refl refl) counit₀ comult₀ lunit-ax₀ runit-ax₀ assoc-ax₀) refl) 
     (⟦⌈⌉⟧₀-lem (Shape₁ ◁ Pos₁) (CM (Functor⋆ (λ X → ∃ Shape₁ (λ s → Pos₁ s → X)) (λ f r' → ∃.fst∃ r' , (λ x → f (∃.snd∃ r' x))) refl refl) counit₁ comult₁ lunit-ax₁ runit-ax₁ assoc-ax₁) refl ) 
     (λ X → ext (λ a → cong' (refl {a = (∃.fst∃ a , (λ x → x))}) refl (nat (tr' τ) (∃.snd∃ a))))
