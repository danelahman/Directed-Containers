{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers renaming (⌜_⌝ to ⌜_⌝' ; _⇒_ to _⇒'_ ; ⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁')
open import DContainers renaming (⌈_⌉ to ⌈_⌉')
open import DContainerExt
open import Comonads
open import Functors
open import Comonad2DContainer
open import InterpretQuoteLem2
open import Comonad2DContainer
open import ComonadMorph2DContainerMorph

module FullyFaithfulLem1 where

open Container
open DContainer renaming (Shape to Shape' ; Pos to Pos')
open Functor
open Comonad
open _⇛_
open _⇨_


open DContainers._⇒_

⇒-eq' : {C C' D D' : DContainer}(f : C ⇒ D)(g : C' ⇒ D') → C == C' → D == D' → sf f == sf g → (∀ {s s'} → s == s' → pf f {s} == pf g {s'}) → f == g
⇒-eq' f g refl refl p q = ⇒-eq f g p (λ s → q refl)


fully-faithful-lem1 : {C₀ C₁ : DContainer} → {f : C₀ ⇒ C₁} → (⌜ ⟦ C₀ ⟧₀ , ⟦ C₁ ⟧₀ , refl , refl , ⟦ f ⟧₁ ⌝) == f
fully-faithful-lem1 {C₀} {C₁} {f} = ⇒-eq' 
  ⌜ ⟦ C₀ ⟧₀ , ⟦ C₁ ⟧₀ , refl , refl , ⟦ f ⟧₁ ⌝ 
  f 
  ⌈⟦⟧₀⌉-lem 
  ⌈⟦⟧₀⌉-lem 
  refl 
  (λ x → icong (λ{s} → pf f {s}) x)
