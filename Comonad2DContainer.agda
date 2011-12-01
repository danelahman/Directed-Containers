{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers
open import DContainers renaming (_⇒_ to _⇒'_ ; _∘_ to _∘'_ ; ⇒-id to ⇒-id' ; ∘assoc to ∘assoc')
open import DContainerExt renaming (⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁' ; ⟦⟧₁-id-eq to ⟦⟧₁-id-eq')
open import Comonads renaming (_c∘_ to _c∘'_)
open import Functors

open import Comonad2DContainerHelper
open import Comonad2DContainerHelper2
open import Comonad2DContainerHelper3

module Comonad2DContainer where

open Container
open Containers._⇒_
open Functor
open Comonad
open Functors._⇛_

⌈_,_⌉ : (CM : Comonad) → {C : Container} → (Fun CM == ⟦ C ⟧₀) → DContainer
⌈_,_⌉ (CM .(Functor⋆ (λ X → ∃ (Shape C) (λ s → (Pos C) s → X)) (fmap'.fmap' (Shape C) (Pos C)) refl refl) counit comult lunit runit assoc) {C} refl = _◁_ Shape' Pos' _↓'_ o' _⊕'_ ax1' ax2' ax3' ax4' ax5' module c2dc where
  counit'' : ⟦ C ⟧₀ ⇛ ⟦ Id-Con ⟧₀
  counit'' = NatIso.j e-iso ∘ counit

  counit' : C ⇒ Id-Con
  counit' = ⌜ counit'' ⌝

  comult'' : ⟦ C ⟧₀ ⇛ ⟦ C [ C ] ⟧₀
  comult'' = NatIso.j (m-iso C C ) ∘ comult

  comult' : C ⇒ C [ C ]
  comult' = ⌜ comult'' ⌝
  
  abstract
    comult'-ax1 : ∀ {s} → ∃.fst∃ (tr comult (s , identity)) == s
    comult'-ax1 {s} = cong'  refl refl (cong sf (fully-faithful-lem3-c {_} {_} {(⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C (Id-Con)) ⌝) ◦ (C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} {⇒-id {C}} (runit-lem {C} {counit} {comult} {runit})))

  Shape' : Set
  Shape' = Shape C

  Pos' : Shape' → Set
  Pos' = Pos C

  o' : {s : Shape'} → Pos' s
  o' {s} = pf counit' s tt

  _↓'_ : (s : Shape') → Pos' s → Shape'
  s ↓' p = ∃.snd∃ (sf comult' s) (subst Pos' p (sym comult'-ax1))

  _⊕'_ : {s : Shape'} → (p : Pos' s) → Pos' (s ↓' p) → Pos' s
  _⊕'_ {s} p p' = pf comult' s (subst Pos' p (sym comult'-ax1) , p')

  abstract
    ax1' : {s : Shape'} → s ↓' o' == s
    ax1' {s} = trans 
      (cong 
       (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
       (trans (stripsubst (Pos C) (tr counit (s , identity)) (sym comult'-ax1)) (cong' (sym comult'-ax1) refl {λ x → tr counit (x , identity)} {λ x → tr counit (x , identity)} refl))) 
      (cong' 
       refl refl 
       (cong sf 
        (fully-faithful-lem3-c 
         {_} {_} 
         {(⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso (Id-Con) C) ⌝) ◦ (⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} 
         {⇒-id {C}} 
         (lunit-lem {C} {counit} {comult} {lunit}))))

  abstract
    ax2' : {s : Shape'} → {p : Pos' s} → {p' : Pos' (s ↓' p)} → s ↓' p ⊕' p' == s ↓' p ↓' p'
    ax2' {s} {p} {p'} = sym 
     (trans 
       (cong' {_} {_} 
       {subst (Pos C) p' (sym (comult'-ax1 {∃.fst∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1)))}))} 
       {subst (Pos C) p' 
        (cong2 
         (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) 
         (sym comult'-ax1) 
         (trans 
          (stripsubst (Pos C) p (sym comult'-ax1)) 
           (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))))}
       (trans 
        (stripsubst (Pos C) p' (sym comult'-ax1)) 
        (sym 
         (stripsubst (Pos C) p' 
          (cong2 
           (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) 
           (sym comult'-ax1) 
           (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))))))) 
       (ext' (λ _ → refl)) 
       (∃-eqsnd refl refl 
        (cong' {_} {_} 
         {subst (Pos C) p (sym comult'-ax1)} 
         {subst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))} 
         (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))) 
         (ext' (λ _ → refl))
         (∃-eqsnd refl refl 
          (cong' {_} {_} {s} {s} refl refl 
           (cong sf 
            (fully-faithful-lem3-c {_} {_} 
             {(C C◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} 
             {(α-iso1 C C C) ◦ (⌜ NatIso.j (m-iso C C ) ∘ comult ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} 
             (assoc-lem {C} {counit} {comult} {assoc})))))))) 
     (cong 
      (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x))
      (trans 
       (cong3 
        (λ x y z → ∃.snd∃ (∃.snd∃ (tr comult (x , identity)) y) z) 
        comult'-ax1 
        (trans 
         (stripsubst (Pos C) p 
          (trans (sym comult'-ax1) (sym comult'-ax1))) 
         (sym (stripsubst (Pos C) p (sym comult'-ax1)))) 
        (stripsubst (Pos C) p' 
         (cong2 
          (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) 
          (sym comult'-ax1) 
          (trans 
           (stripsubst (Pos C) p (sym comult'-ax1)) 
           (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1)))))))) 
       (sym 
        (stripsubst (Pos C) (∃.snd∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1))) p') (sym comult'-ax1))))))

  abstract
    ax3' : {s : Shape'} → (p : Pos' s) → p ⊕' o' == p
    ax3' {s} p = cong' 
     (stripsubst (Pos C) p (sym comult'-ax1)) 
     (ext' (λ x → refl)) 
     (cong2 pf 
      (fully-faithful-lem3-c {_} {_} 
       {(⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C (Id-Con)) ⌝) ◦ (C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} 
       {⇒-id {C}} (runit-lem {C} {counit} {comult} {runit})) 
      refl)

  abstract
    ax4' : {s : Shape'} → (p : Pos' (s ↓' o')) → o' ⊕' p == p
    ax4' {s} p =  trans 
     ((cong2'' 
      refl refl {λ x y → ∃.snd∃ (∃.snd∃ (tr comult (s , identity)) x) y} {λ x y → ∃.snd∃ (∃.snd∃ (tr comult (s , identity)) x) y} refl 
      (trans 
       (stripsubst (Pos C) (tr counit (s , identity)) (sym comult'-ax1)) 
       (cong' (sym comult'-ax1) refl {λ x → tr counit (x , identity)} {λ x → tr counit (x , identity)} refl)) 
      (sym (stripsubst 
       (λ x → Pos C (∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x))) p 
       (trans 
        (stripsubst (Pos C) (tr counit (s , identity)) (sym comult'-ax1)) 
        (cong' 
         (sym comult'-ax1) 
         refl {λ x → tr counit (x , identity)} {λ x → tr counit (x , identity)} refl)))))) 
     (cong' 
      (stripsubst 
       (λ x → Pos C (∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x))) p 
       (trans 
        (stripsubst (Pos C) (tr counit (s , identity)) (sym comult'-ax1)) 
        (cong' 
         (sym comult'-ax1) 
         refl {λ x → tr counit (x , identity)} {λ x → tr counit (x , identity)} refl))) 
      (ext' (λ x → cong (Pos C) (sym ax1'))) 
      (cong2 pf 
       (fully-faithful-lem3-c 
        {_} {_} 
        {(⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso (Id-Con) C) ⌝) ◦ (⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} 
        {⇒-id {C}} 
        (lunit-lem {C} {counit} {comult} {lunit})) 
       (sym ax1')))

  abstract
    ax5' : {s : Shape'} → (p : Pos' s) → (p' : Pos' (s ↓' p)) → (p'' : Pos' (s ↓' p ⊕' p')) → p ⊕' p' ⊕' p'' == p ⊕' (p' ⊕' (subst Pos' p'' ax2'))
    ax5' {s} p p' p'' = sym (
     trans 
      (cong' {_} {_} 
       {(subst (Pos C) p (sym comult'-ax1)) , ((subst (Pos C) p' (sym comult'-ax1)) , (subst (Pos C) p'' (ax2' {s} {p} {p'})))} 
       {(subst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))) , 
        ((subst (Pos C) p' 
         (cong2 
          (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) 
          (sym comult'-ax1) 
          (trans 
           (stripsubst (Pos C) p (sym comult'-ax1)) 
           (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))))) , 
        (subst (Pos C) p'' 
         (cong 
          (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
          (trans 
           (stripsubst (Pos C) (∃.snd∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1))) p') (sym comult'-ax1)) 
           (cong3 
            (λ x y z → ∃.snd∃ (∃.snd∃ (tr comult (x , identity)) y) z) 
            (sym comult'-ax1) 
            (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))) 
            (sym 
             (stripsubst (Pos C) p' 
              (cong2 
               (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) 
               (sym comult'-ax1) 
               (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1)))))))))))))} 
       (∃-eq 
        (ext' 
         (λ {p0} {p1} q → cong2 
          (λ x y → ∃ (Pos C x) y) 
           (trans 
            comult'-ax1 
            (cong2 (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) (sym comult'-ax1) q)) 
          (ext' (λ {p2} {p3} q' → 
           cong (Pos C) 
            (trans 
             (cong2 
              (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x) , identity)) y)) 
              (trans 
               (sym (stripsubst (Pos C) p0 comult'-ax1)) 
               (sym (stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1)))) 
              (trans 
               (sym 
                (stripsubst (Pos C) p2 
                 (trans 
                  comult'-ax1 
                  (cong 
                   (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
                   (trans 
                    (sym (stripsubst (Pos C) p0 comult'-ax1)) 
                    (sym (stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1)))))))) 
               (sym 
                (stripsubst (Pos C) 
                 (subst (Pos C) p2 
                  (trans 
                   comult'-ax1 
                   (cong 
                    (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
                    (trans 
                     (sym (stripsubst (Pos C) p0 comult'-ax1)) 
                     (sym (stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1))))))) 
                 (sym comult'-ax1))))) 
            (trans 
             (sym 
              (ax2' {s} {subst (Pos C) p0 comult'-ax1} 
               {subst (Pos C) p2 
                (trans 
                 (comult'-ax1) 
                 (cong 
                  (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
                  (trans 
                   (sym (stripsubst (Pos C) p0 comult'-ax1)) 
                   (sym ((stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1)))))))})) 
             (cong 
              (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
              (trans 
               (stripsubst (Pos C) 
                (∃.snd∃ 
                 (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1))) 
                 (subst (Pos C) p2 
                  (trans 
                   comult'-ax1 
                   (cong 
                    (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
                    (trans 
                     (sym (stripsubst (Pos C) p0 comult'-ax1)) 
                     (sym (stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1)))))))) 
                (sym comult'-ax1)) 
               (cong3 
                (λ x y z → ∃.snd∃ (∃.snd∃ (tr comult (x , identity)) y) z) 
                (sym comult'-ax1) 
                (trans 
                 (stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1)) 
                 (trans (stripsubst (Pos C) p0 comult'-ax1) q)) 
                (trans 
                 (stripsubst (Pos C) p2  
                  (trans 
                   comult'-ax1 
                   (cong 
                    (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
                    (trans 
                     (sym (stripsubst (Pos C) p0 comult'-ax1)) 
                     (sym (stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1))))))) 
                 q')))))))))) 
        (trans 
         (stripsubst (Pos C) p (sym comult'-ax1)) 
         (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))) 
        (∃-eq 
         (ext' (λ {p0} {p1} q → 
          cong (Pos C) 
           (trans 
            (cong 
             (λ x → ∃.fst∃ (∃.snd∃ (tr comult (∃.fst∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1))) , identity)) x)) 
             (trans 
              (sym (stripsubst (Pos C) p0 comult'-ax1)) 
              (sym (stripsubst (Pos C) (subst (Pos C) p0 comult'-ax1) (sym comult'-ax1))))) 
            (trans 
             (sym (ax2' {s} {p} {subst (Pos C) p0 comult'-ax1})) 
             (cong 
              (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
              (trans 
               (stripsubst (Pos C) 
                (∃.snd∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1))) (subst (Pos C) p0 comult'-ax1)) 
                (sym comult'-ax1)) 
               (cong3 
                (λ x y z → ∃.snd∃ (∃.snd∃ (tr comult (x , identity)) y) z) 
                (sym comult'-ax1) 
                (trans 
                 (stripsubst (Pos C) p (sym comult'-ax1)) 
                 (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))) 
                (trans 
                 (stripsubst (Pos C) p0 comult'-ax1) 
                 q)))))))) 
         (trans 
          (stripsubst (Pos C) p' (sym comult'-ax1)) 
          (sym (stripsubst (Pos C) p' (cong2 (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) (sym comult'-ax1) (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))))))) 
         (trans 
          (stripsubst (Pos C) p'' ax2') 
          (sym (stripsubst (Pos C) p'' (cong (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) (trans (stripsubst (Pos C) (∃.snd∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1))) p') (sym comult'-ax1)) (cong3 (λ x y z → ∃.snd∃ (∃.snd∃ (tr comult (x , identity)) y) z) (sym comult'-ax1) (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))) (sym (stripsubst (Pos C) p' (cong2 (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) (sym comult'-ax1) (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1)))))))))))))))) 
        (ext' (λ _ → refl)) 
        (cong2 
         pf 
         (fully-faithful-lem3-c {_} {_} {(C C◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝}  {(α-iso1 C C C) ◦ (⌜ NatIso.j (m-iso C C ) ∘ comult ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} (assoc-lem {C} {counit} {comult} {assoc})) 
         {s} 
         {s} 
         refl)) 
       (cong2 
        (λ x y → ∃.snd∃ (∃.snd∃ (tr comult (s , identity)) x) y) 
        (trans 
         (cong3 
          (λ x y z → ∃.snd∃ (∃.snd∃ (tr comult (x , identity)) y) z) 
          comult'-ax1 
          (trans (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))) (sym (stripsubst (Pos C) p (sym comult'-ax1)))) 
          (stripsubst (Pos C) p' 
           (cong2 
            (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) 
            (sym comult'-ax1) 
            (trans 
             (stripsubst (Pos C) p (sym comult'-ax1)) 
             (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1)))))))) 
         (sym (stripsubst (Pos C) (∃.snd∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1))) p') (sym comult'-ax1)))) 
        (stripsubst (Pos C) p'' 
         (cong 
          (λ x → ∃.fst∃ (∃.snd∃ (tr comult (s , identity)) x)) 
          (trans 
           (stripsubst (Pos C) (∃.snd∃ (∃.snd∃ (tr comult (s , identity)) (subst (Pos C) p (sym comult'-ax1))) p') (sym comult'-ax1)) 
           (cong3 
            (λ x y z → ∃.snd∃ (∃.snd∃ (tr comult (x , identity)) y) z) 
            (sym comult'-ax1) 
            (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))) 
            (sym 
             (stripsubst (Pos C) p' 
              (cong2 
               (λ x y → ∃.fst∃ (∃.snd∃ (tr comult (x , identity)) y)) 
               (sym comult'-ax1) 
               (trans (stripsubst (Pos C) p (sym comult'-ax1)) (sym (stripsubst (Pos C) p (trans (sym comult'-ax1) (sym comult'-ax1))))))))))))))

  infixl 50 _↓'_
  infixl 60 _⊕'_

