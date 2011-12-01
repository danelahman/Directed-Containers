{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers
open import DContainers renaming (_⇒_ to _⇒'_ ; _∘_ to _∘'_ ; ∘assoc to ∘assoc')
open import DContainerExt renaming (⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁')
open import Comonads renaming (_c∘_ to _c∘'_)
open import Functors
open import Comonad2DContainer

module ComonadMorph2DContainerMorphHelper where

open Container
open DContainer renaming (Shape to Shape' ; Pos to Pos')
open Containers._⇒_
open Functor
open Comonad
open _⇛_
open _⇨_

abstract
  cu-lem : {C₀ C₁  : Container} → {counit₀ : ⟦ C₀ ⟧₀ ⇛ Id-Fun} → {comult₀ : ⟦ C₀ ⟧₀ ⇛ (⟦ C₀ ⟧₀ ⋆ ⟦ C₀ ⟧₀)} → {lunit₀ : (counit₀ ∘F ⟦ C₀ ⟧₀) ∘ comult₀ == ⇛-id {⟦ C₀ ⟧₀}} → {runit₀ : (⟦ C₀ ⟧₀ F∘ counit₀) ∘ comult₀ == ⇛-id {⟦ C₀ ⟧₀}} → {assoc₀ : (comult₀ ∘F ⟦ C₀ ⟧₀) ∘ comult₀ == (⟦ C₀ ⟧₀ F∘ comult₀) ∘ comult₀} → {counit₁ : ⟦ C₁ ⟧₀ ⇛ Id-Fun} → {comult₁ : ⟦ C₁ ⟧₀ ⇛ (⟦ C₁ ⟧₀ ⋆ ⟦ C₁ ⟧₀)} → {lunit₁ : (counit₁ ∘F ⟦ C₁ ⟧₀) ∘ comult₁ == ⇛-id {⟦ C₁ ⟧₀}} → {runit₁ : (⟦ C₁ ⟧₀ F∘ counit₁) ∘ comult₁ == ⇛-id {⟦ C₁ ⟧₀}} → {assoc₁ : (comult₁ ∘F ⟦ C₁ ⟧₀) ∘ comult₁ == (⟦ C₁ ⟧₀ F∘ comult₁) ∘ comult₁} → {h : CM (Functor⋆ (λ X → ∃ (Shape C₀) (λ s → Pos C₀ s → X)) (fmap'.fmap' (Shape C₀) (Pos C₀)) refl refl) counit₀ comult₀ lunit₀ runit₀ assoc₀ ⇨ CM (Functor⋆ (λ X → ∃ (Shape C₁) (λ s → Pos C₁ s → X)) (fmap'.fmap' (Shape C₁) (Pos C₁)) refl refl) counit₁ comult₁ lunit₁ runit₁ assoc₁} → ⟦ ⌜ NatIso.j e-iso ∘ counit₁ ⌝ ◦ ⌜ tr' h ⌝ ⟧₁ == ⟦ ⌜ NatIso.j e-iso ∘ counit₀ ⌝ ⟧₁
  cu-lem {C₀} {C₁} {counit₀} {comult₀} {lunit₀} {runit₀} {assoc₀} {counit₁} {comult₁} {lunit₁} {runit₁} {assoc₁} {h} = 
   trans 
    (⟦⟧₁-dist {_} {_} {_} {⌜ NatIso.j e-iso ∘ counit₁ ⌝} {⌜ tr' h ⌝}) 
    (trans 
     (cong (λ x → ⟦ ⌜ NatIso.j e-iso ∘ counit₁ ⌝ ⟧₁ ∘ x) (fully-faithful-lem2-c {_} {_} {tr' h})) 
     (trans 
      (cong (λ x → x ∘ tr' h) (fully-faithful-lem2-c {_} {_} {NatIso.j e-iso ∘ counit₁})) 
      (trans 
       (trans 
        (∘assoc {_} {_} {_} {_} {NatIso.j e-iso} {counit₁} {tr' h}) 
        (cong (λ x → NatIso.j e-iso ∘ x) (cu h))) 
       (sym (fully-faithful-lem2-c {_} {_} {NatIso.j e-iso ∘ counit₀})))))
abstract
  m-iso-lem : {C₀ C₁ : Container}(h : C₀ ⇒ C₁) → ⟦ h ◦C C₀ ⟧₁ ∘ NatIso.j (m-iso C₀ C₀) == NatIso.j (m-iso C₁ C₀) ∘ (⟦ h ⟧₁ ∘F ⟦ C₀ ⟧₀)
  m-iso-lem h = nat-eq _ _ (λ {X} → refl) 

abstract
  m-iso-lem' : {C₀ C₁ : Container}(h : C₀ ⇒ C₁) → ⟦ C₁ C◦ h ⟧₁ ∘ NatIso.j (m-iso C₁ C₀) == NatIso.j (m-iso C₁ C₁) ∘ (⟦ C₁ ⟧₀ F∘ ⟦ h ⟧₁)
  m-iso-lem' h = nat-eq _ _ (λ {X} → refl)
 
abstract            
  cm-lem : {C₀ C₁  : Container} → 
         {counit₀ : ⟦ C₀ ⟧₀ ⇛ Id-Fun} → 
         {comult₀ : ⟦ C₀ ⟧₀ ⇛ (⟦ C₀ ⟧₀ ⋆ ⟦ C₀ ⟧₀)} → 
         {lunit₀ : (counit₀ ∘F ⟦ C₀ ⟧₀) ∘ comult₀ == ⇛-id {⟦ C₀ ⟧₀}} → 
         {runit₀ : (⟦ C₀ ⟧₀ F∘ counit₀) ∘ comult₀ == ⇛-id {⟦ C₀ ⟧₀}} → 
         {assoc₀ : (comult₀ ∘F ⟦ C₀ ⟧₀) ∘ comult₀ == (⟦ C₀ ⟧₀ F∘ comult₀) ∘ comult₀} → 
         {counit₁ : ⟦ C₁ ⟧₀ ⇛ Id-Fun} → 
         {comult₁ : ⟦ C₁ ⟧₀ ⇛ (⟦ C₁ ⟧₀ ⋆ ⟦ C₁ ⟧₀)} → 
         {lunit₁ : (counit₁ ∘F ⟦ C₁ ⟧₀) ∘ comult₁ == ⇛-id {⟦ C₁ ⟧₀}} → 
         {runit₁ : (⟦ C₁ ⟧₀ F∘ counit₁) ∘ comult₁ == ⇛-id {⟦ C₁ ⟧₀}} → 
         {assoc₁ : (comult₁ ∘F ⟦ C₁ ⟧₀) ∘ comult₁ == (⟦ C₁ ⟧₀ F∘ comult₁) ∘ comult₁} → 
         {h : CM (Functor⋆ (λ X → ∃ (Shape C₀) (λ s → Pos C₀ s → X)) (fmap'.fmap' (Shape C₀) (Pos C₀)) refl refl) counit₀ comult₀ lunit₀ runit₀ assoc₀ ⇨ CM (Functor⋆ (λ X → ∃ (Shape C₁) (λ s → Pos C₁ s → X)) (fmap'.fmap' (Shape C₁) (Pos C₁)) refl refl) counit₁ comult₁ lunit₁ runit₁ assoc₁} → 
         ⟦ ⌜ NatIso.j (m-iso C₁ C₁ ) ∘ comult₁ ⌝ ◦ ⌜ tr' h ⌝ ⟧₁ == ⟦ (C₁ C◦ ⌜ tr' h ⌝) ◦ (⌜ tr' h ⌝ ◦C C₀) ◦ ⌜ NatIso.j (m-iso C₀ C₀ ) ∘ comult₀ ⌝ ⟧₁
  cm-lem {C₀} {C₁} {counit₀} {comult₀} {lunit₀} {runit₀} {assoc₀} {counit₁} {comult₁} {lunit₁} {runit₁} {assoc₁} {h} = 
   trans 
    (⟦⟧₁-dist {_} {_} {_} {⌜ NatIso.j (m-iso C₁ C₁) ∘ comult₁ ⌝} {⌜ tr' h ⌝}) 
    (trans 
     (cong (λ x → ⟦ ⌜ NatIso.j (m-iso C₁ C₁) ∘ comult₁ ⌝ ⟧₁ ∘ x) (fully-faithful-lem2-c {_} {_} {tr' h})) 
     (trans 
      (cong (λ x → x ∘ tr' h) (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C₁ C₁) ∘ comult₁})) 
      (sym (trans 
       (⟦⟧₁-dist {_} {_} {_} {(C₁ C◦ ⌜ tr' h ⌝) ◦ (⌜ tr' h ⌝ ◦C C₀)} {⌜ NatIso.j (m-iso C₀ C₀) ∘ comult₀ ⌝}) 
       (trans 
        (cong 
         (λ x → ⟦ (C₁ C◦ ⌜ tr' h ⌝) ◦ (⌜ tr' h ⌝ ◦C C₀) ⟧₁ ∘ x) 
         (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C₀ C₀) ∘ comult₀})) 
        (trans 
         (cong 
          (λ x → x ∘ (NatIso.j (m-iso C₀ C₀) ∘ comult₀)) 
          (⟦⟧₁-dist {_} {_} {_} {C₁ C◦ ⌜ tr' h ⌝} {⌜ tr' h ⌝ ◦C C₀})) 
         (trans 
          (∘assoc {_} {_} {_} {_} {⟦ C₁ C◦ ⌜ tr' h ⌝ ⟧₁} {⟦ ⌜ tr' h ⌝ ◦C C₀ ⟧₁} {NatIso.j (m-iso C₀ C₀) ∘ comult₀}) 
          (trans 
           (cong 
            (λ x → ⟦ C₁ C◦ ⌜ tr' h ⌝ ⟧₁ ∘ x) 
            (sym (∘assoc {_} {_} {_} {_} {⟦ ⌜ tr' h ⌝ ◦C C₀ ⟧₁} {NatIso.j (m-iso C₀ C₀)} {comult₀}))) 
           (trans 
            (cong 
             (λ x → ⟦ C₁ C◦ ⌜ tr' h ⌝ ⟧₁ ∘ (x ∘ comult₀)) 
             (nat-eq 
              (⟦ ⌜ tr' h ⌝ ◦C C₀ ⟧₁ ∘ NatIso.j (m-iso C₀ C₀)) 
              (NatIso.j (m-iso C₁ C₀) ∘ (tr' h ∘F ⟦ C₀ ⟧₀)) 
              ( λ {X} → cong 
               (λ α → tr α {X}) 
               (trans 
                (m-iso-lem ⌜ tr' h ⌝) 
                (cong 
                 (λ x → NatIso.j (m-iso C₁ C₀) ∘ (x ∘F ⟦ C₀ ⟧₀)) 
                 (fully-faithful-lem2-c {f = tr' h}))) ) )) 
            (trans 
             (sym (∘assoc {_} {_} {_} {_} {⟦ C₁ C◦ ⌜ tr' h ⌝ ⟧₁} {NatIso.j (m-iso C₁ C₀) ∘ (tr' h ∘F ⟦ C₀ ⟧₀)} {comult₀})) 
             (trans 
              (cong 
               (λ x → x ∘ comult₀) 
               (sym (∘assoc {_} {_} {_} {_} {⟦ C₁ C◦ ⌜ tr' h ⌝ ⟧₁} {NatIso.j (m-iso C₁ C₀)} {tr' h ∘F ⟦ C₀ ⟧₀}))) 
               (trans 
                (cong 
                 (λ x → x ∘ (tr' h ∘F ⟦ C₀ ⟧₀) ∘ comult₀) 
                 (nat-eq 
                  (⟦ C₁ C◦ ⌜ tr' h ⌝ ⟧₁ ∘ NatIso.j (m-iso C₁ C₀)) 
                  (NatIso.j (m-iso C₁ C₁) ∘ (⟦ C₁ ⟧₀ F∘ tr' h)) 
                  ( λ {X} → cong 
                   (λ α → tr α {X}) 
                   (trans 
                    (m-iso-lem' ⌜ tr' h ⌝) 
                    (cong 
                     (λ x → NatIso.j (m-iso C₁ C₁) ∘ (⟦ C₁ ⟧₀ F∘ x)) 
                     (fully-faithful-lem2-c {f = tr' h}))) ))) 
               (trans 
                (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso C₁ C₁) ∘ (⟦ C₁ ⟧₀ F∘ tr' h)} {tr' h ∘F ⟦ C₀ ⟧₀} {comult₀}) 
                (trans 
                 (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso C₁ C₁)} {⟦ C₁ ⟧₀ F∘ tr' h} {(tr' h ∘F ⟦ C₀ ⟧₀) ∘ comult₀}) 
                 (trans 
                  (cong (λ x → NatIso.j (m-iso C₁ C₁) ∘ x) (sym (∘assoc {_} {_} {_} {_} {⟦ C₁ ⟧₀ F∘ tr' h} {tr' h ∘F ⟦ C₀ ⟧₀} {comult₀}))) 
                  (trans 
                   (cong 
                    (λ x → NatIso.j (m-iso C₁ C₁) ∘ x) 
                    (sym (cm h))) 
                   (sym (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso C₁ C₁)} {comult₁} {tr' h}))))))))))))))))))
