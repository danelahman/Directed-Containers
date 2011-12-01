{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers
open import DContainers renaming (_∘_ to _∘'_ ; ⇒-id to ⇒-id' ; ⌈_⌉ to ⌈_⌉' ; _⇒_ to _⇒'_)
open import DContainerExt renaming (⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁') 
open import Comonads renaming (_c∘_ to _c∘'_)
open import Functors
open import Comonad2DContainer

open import Comonad2DContainerHelper
open import ComonadMorph2DContainerMorphHelper

module ComonadMorph2DContainerMorph where

open Container
open DContainer renaming (Shape to Shape' ; Pos to Pos')
open Containers._⇒_
open Functor
open Comonad
open _⇛_
open _⇨_

⌜_,_,_,_,_⌝ : (CM₀ CM₁ : Comonad) → {C₀ C₁ : Container} → (q₀ : Fun CM₀ == ⟦ C₀ ⟧₀) → (q₁ : Fun CM₁ == ⟦ C₁ ⟧₀) → CM₀ ⇨ CM₁ → ⌈ CM₀ , q₀ ⌉ ⇒' ⌈ CM₁ , q₁ ⌉
⌜_,_,_,_,_⌝ (CM .(Functor⋆ (λ X → ∃ (Shape C₀) (λ s → (Pos C₀) s → X)) (fmap'.fmap' (Shape C₀) (Pos C₀)) refl refl) counit₀ comult₀ lunit₀ runit₀ assoc₀) (CM .(Functor⋆ (λ X → ∃ (Shape C₁) (λ s → (Pos C₁) s → X)) (fmap'.fmap' (Shape C₁) (Pos C₁)) refl refl) counit₁ comult₁ lunit₁ runit₁ assoc₁) {C₀} {C₁} refl refl h = _◁_ sf' pf' ax6' ax7' ax8' where
  C₀' : DContainer
  C₀' = ⌈ (CM (Functor⋆ (λ X → ∃ (Shape C₀) (λ s → (Pos C₀) s → X)) (fmap'.fmap' (Shape C₀) (Pos C₀)) refl refl) counit₀ comult₀ lunit₀ runit₀ assoc₀) , refl ⌉

  C₁' : DContainer
  C₁' = ⌈ (CM (Functor⋆ (λ X → ∃ (Shape C₁) (λ s → (Pos C₁) s → X)) (fmap'.fmap' (Shape C₁) (Pos C₁)) refl refl) counit₁ comult₁ lunit₁ runit₁ assoc₁) , refl ⌉

  counit₀' : C₀ ⇒ Id-Con
  counit₀' = ⌜ NatIso.j e-iso ∘ counit₀ ⌝

  comult₀' : C₀ ⇒ C₀ [ C₀ ]
  comult₀' = ⌜ NatIso.j (m-iso C₀ C₀ ) ∘ comult₀ ⌝

  counit₁' : C₁ ⇒ Id-Con
  counit₁' = ⌜ NatIso.j e-iso ∘ counit₁ ⌝

  comult₁' : C₁ ⇒ C₁ [ C₁ ]
  comult₁' = ⌜ NatIso.j (m-iso C₁ C₁ ) ∘ comult₁ ⌝

  abstract
    comult₀'-ax1 : ∀ {s} → ∃.fst∃ (tr comult₀ (s , identity)) == s
    comult₀'-ax1 {s} = cong'  refl refl (cong sf (fully-faithful-lem3-c {_} {_} {(⌜ (⟦ C₀ ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C₀ (Id-Con)) ⌝) ◦ (C₀ C◦ ⌜ NatIso.j e-iso ∘ counit₀ ⌝) ◦ ⌜ NatIso.j (m-iso C₀ C₀ ) ∘ comult₀ ⌝} {⇒-id {C₀}} (runit-lem {C₀} {counit₀} {comult₀} {runit₀})))

  sf' : Shape C₀ → Shape C₁
  sf' s = sf ⌜ tr' h ⌝ s

  pf' : {s : Shape C₀} → Pos C₁ (sf' s) → Pos C₀ s
  pf' {s} p = pf ⌜ tr' h ⌝ s p

  abstract
    ax6' : {s : Shape C₀} → {p : Pos' C₁' (sf' s)} → _↓_ C₁' (sf' s) p == sf' (_↓_ C₀' s (pf' {s} p))
    ax6' {s} {p} = trans 
     (cong' {_} {_} {_} 
      {subst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1)} 
      (trans 
       (stripsubst (Pos C₁) p (sym (c2dc.comult'-ax1 counit₁ comult₁ lunit₁ runit₁ assoc₁))) 
       (sym 
        (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1)))) 
      (ext' (λ x → refl)) 
      (∃-eqsnd refl refl 
       (cong' {_} {_} {s} {s} refl refl 
        (cong sf 
         (fully-faithful-lem3-c {_} {_} 
          {⌜ NatIso.j (m-iso C₁ C₁ ) ∘ comult₁ ⌝ ◦ ⌜ tr' h ⌝} 
          {(C₁ C◦ ⌜ tr' h ⌝) ◦ (⌜ tr' h ⌝ ◦C C₀) ◦ ⌜ NatIso.j (m-iso C₀ C₀ ) ∘ comult₀ ⌝} 
          (cm-lem {C₀} {C₁} {counit₀} {comult₀} {lunit₀} {runit₀} {assoc₀} {counit₁} {comult₁} {lunit₁} {runit₁} {assoc₁} {h})))))) 
     (cong 
      (λ x → ∃.fst∃ (tr (tr' h) (∃.fst∃ (∃.snd∃ (tr comult₀ (s , identity)) x) , identity))) 
      (trans 
       (cong2 
        (λ x y → ∃.snd∃ (tr (tr' h) (x , identity)) y) 
        comult₀'-ax1 
        (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1))) 
       (sym 
        (stripsubst (Pos C₀) (∃.snd∃ (tr (tr' h) (s , identity)) p) (sym (c2dc.comult'-ax1 counit₀ comult₀ lunit₀ runit₀ assoc₀))))))

    ax7' : {s : Shape C₀} → pf' {s} (o C₁') == o C₀' {s}
    ax7' {s}  = cong' refl refl 
     (cong' refl refl 
      (cong pf 
       (fully-faithful-lem3-c {_} {_} 
        {⌜ NatIso.j e-iso ∘ counit₁ ⌝ ◦ ⌜ tr' h ⌝} 
        {⌜ NatIso.j e-iso ∘ counit₀ ⌝} 
        (cu-lem {C₀} {C₁} {counit₀} {comult₀} {lunit₀} {runit₀} {assoc₀} {counit₁} {comult₁} {lunit₁} {runit₁} {assoc₁} {h}))))

    ax8' : {s : Shape C₀} → (p : Pos' C₁' (sf' s)) → (p' : Pos' C₁' (_↓_ C₁' (sf' s) p)) → pf' {s} (_⊕_ C₁' p p') == _⊕_ C₀' (pf' {s} p) (pf' (subst (Pos' C₁') p' ax6'))
    ax8' {s} p p' = trans 
     (cong' {_} {_} {_} 
      {(subst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1)) , 
       (subst (Pos C₁) p' (trans (ax6' {s} {p}) 
        (cong 
         (λ x → ∃.fst∃ (tr (tr' h) (∃.fst∃ (∃.snd∃ (tr comult₀ (s , identity)) x) , identity))) 
         (trans 
          (stripsubst (Pos C₀) (∃.snd∃ (tr (tr' h) (s , identity)) p) (sym (c2dc.comult'-ax1 counit₀ comult₀ lunit₀ runit₀ assoc₀))) 
          (cong2 (λ x y → ∃.snd∃ (tr (tr' h) (x , identity)) y) (sym comult₀'-ax1) (sym (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1))))))))} 
      (∃-eq 
       (ext' (λ {p0} {p1} q → cong (Pos C₁) 
        (trans 
         (cong2 
          (λ x y → ∃.fst∃ (∃.snd∃ (tr comult₁ (∃.fst∃ (tr (tr' h) (x , identity)) , identity)) y)) 
          (sym comult₀'-ax1) 
          (trans q (sym (stripsubst (Pos C₁) p1 (sym (c2dc.comult'-ax1 counit₁ comult₁ lunit₁ runit₁ assoc₁)))))) 
         (trans 
          (ax6' {∃.fst∃ (tr comult₀ (s , identity))} {p1}) 
          (cong2 
           (λ x y → ∃.fst∃ (tr (tr' h) (∃.fst∃ (∃.snd∃ (tr comult₀ (x , identity)) y) , identity))) 
           comult₀'-ax1 
           (stripsubst (Pos C₀) 
            (∃.snd∃ (tr (tr' h) (∃.fst∃ (tr comult₀ (s , identity)) , identity)) p1) 
            (sym (c2dc.comult'-ax1 counit₀ comult₀ lunit₀ runit₀ assoc₀)))))))) 
       (trans 
        (stripsubst (Pos C₁) p (sym (c2dc.comult'-ax1 counit₁ comult₁ lunit₁ runit₁ assoc₁))) 
        (sym (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1)))) 
       (sym 
        (stripsubst (Pos C₁) p' 
         (trans 
          ax6' 
          (cong 
           (λ x → ∃.fst∃ (tr (tr' h) (∃.fst∃ (∃.snd∃ (tr comult₀ (s , identity)) x) , identity))) 
           (trans 
            (stripsubst (Pos C₀) (∃.snd∃ (tr (tr' h) (s , identity)) p) (sym (c2dc.comult'-ax1 counit₀ comult₀ lunit₀ runit₀ assoc₀))) 
            (cong2 
             (λ x y → ∃.snd∃ (tr (tr' h) (x , identity)) y) 
             (sym comult₀'-ax1) 
             (sym (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1)))))))))) 
      (ext' (λ x → refl)) 
      (cong2 pf 
       (fully-faithful-lem3-c {_} {_} 
        {⌜ NatIso.j (m-iso C₁ C₁ ) ∘ comult₁ ⌝ ◦ ⌜ tr' h ⌝} 
        {(C₁ C◦ ⌜ tr' h ⌝) ◦ (⌜ tr' h ⌝ ◦C C₀) ◦ ⌜ NatIso.j (m-iso C₀ C₀ ) ∘ comult₀ ⌝} 
        (cm-lem {C₀} {C₁} {counit₀} {comult₀} {lunit₀} {runit₀} {assoc₀} {counit₁} {comult₁} {lunit₁} {runit₁} {assoc₁} {h})) 
       refl)) 
     (cong2 
      (λ x y → ∃.snd∃ (∃.snd∃ (tr comult₀ (s , identity)) x) y) 
      (trans 
       (cong2 
        (λ x y → ∃.snd∃ (tr (tr' h) (x , identity)) y) 
        comult₀'-ax1 
        (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1))) 
       (sym 
        (stripsubst (Pos C₀) (∃.snd∃ (tr (tr' h) (s , identity)) p) (sym (c2dc.comult'-ax1 counit₀ comult₀ lunit₀ runit₀ assoc₀))))) 
      (cong2 
     (λ x y → ∃.snd∃ (tr (tr' h) (∃.fst∃ (∃.snd∃ (tr comult₀ (s , identity)) x) , identity)) y) 
       (trans 
        (cong2 (λ y z → ∃.snd∃ (tr (tr' h) (y , identity)) z) comult₀'-ax1 (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1))) 
        (sym (stripsubst (Pos C₀) (∃.snd∃ (tr (tr' h) (s , identity)) p) (sym (c2dc.comult'-ax1 counit₀ comult₀ lunit₀ runit₀ assoc₀))))) 
       (trans 
        (stripsubst (Pos C₁) p' 
         (trans 
          ax6' 
          (cong 
           (λ x → ∃.fst∃ (tr (tr' h) (∃.fst∃ (∃.snd∃ (tr comult₀ (s , identity)) x) , identity))) 
           (trans 
            (stripsubst (Pos C₀) (∃.snd∃ (tr (tr' h) (s , identity)) p) (sym (c2dc.comult'-ax1 counit₀ comult₀ lunit₀ runit₀ assoc₀))) 
            (cong2 
             (λ x y → ∃.snd∃ (tr (tr' h) (x , identity)) y) 
             (sym comult₀'-ax1) 
             (sym (stripsubst (λ x → Pos C₁ (∃.fst∃ (tr (tr' h) (x , identity)))) p (sym comult₀'-ax1)))))))) 
        (sym (stripsubst (Pos C₁) p' ax6')))))