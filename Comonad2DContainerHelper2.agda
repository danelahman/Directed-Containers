{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers
open import DContainers renaming (_⇒_ to _⇒'_ ; _∘_ to _∘'_ ; ⇒-id to ⇒-id' ; ∘assoc to ∘assoc')
open import DContainerExt renaming (⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁' ; ⟦⟧₁-id-eq to ⟦⟧₁-id-eq')
open import Comonads renaming (_c∘_ to _c∘'_)
open import Functors

module Comonad2DContainerHelper2 where

open Container
open Containers._⇒_
open Functor
open Comonad
open Functors._⇛_

abstract
  lunit-lem : {C : Container} → {counit : ⟦ C ⟧₀ ⇛ Id-Fun} → {comult : ⟦ C ⟧₀ ⇛ (⟦ C ⟧₀ ⋆ ⟦ C ⟧₀)} → {lunit : (counit ∘F ⟦ C ⟧₀) ∘ comult == ⇛-id {⟦ C ⟧₀}} → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ◦ (⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ⟧₁ == ⟦ ⇒-id {C} ⟧₁
  lunit-lem {C} {counit} {comult} {lunit} = trans 
   (⟦⟧₁-dist {_} {_} {_} {⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝} {(⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝}) 
   (trans 
    (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ x) (⟦⟧₁-dist {_} {_} {_} {(⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C)} {⌜ NatIso.j (m-iso C C) ∘ comult ⌝})) 
    (trans 
     (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ (⟦ ⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C ⟧₁ ∘ x)) (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C C) ∘ comult})) 
     (trans 
      (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ x) (sym (∘assoc {_} {_} {_} {_} {⟦ ⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C ⟧₁} {NatIso.j (m-iso C C)} {comult}))) 
      (trans 
       (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ (x ∘ comult)) (nat-eq (⟦ ⌜ NatIso.j e-iso ∘ counit ⌝ ◦C C ⟧₁ ∘ NatIso.j (m-iso C C)) (NatIso.j (m-iso Id-Con C) ∘ (⟦ ⌜ NatIso.j e-iso ∘ counit ⌝ ⟧₁ ∘F ⟦ C ⟧₀)) (ext (λ _ → cong2 _,_ refl refl)))) 
       (trans 
        (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ x) (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso Id-Con C)} {⟦ ⌜ NatIso.j e-iso ∘ counit ⌝ ⟧₁ ∘F ⟦ C ⟧₀} {comult})) 
        (trans 
         (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ (NatIso.j (m-iso Id-Con C) ∘ ((x ∘F ⟦ C ⟧₀) ∘ comult))) (fully-faithful-lem2-c {_} {_} {NatIso.j e-iso ∘ counit})) 
         (trans 
          (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ (NatIso.j (m-iso Id-Con C) ∘ (x ∘ comult))) (∘Fdist {⟦ C ⟧₀} {_} {_} {_} {NatIso.j e-iso} {counit})) 
          (trans 
           (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ (NatIso.j (m-iso Id-Con C) ∘ x)) (∘assoc {_} {_} {_} {_} {NatIso.j e-iso ∘F ⟦ C ⟧₀} {counit ∘F ⟦ C ⟧₀} {comult})) 
           (trans 
            (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ (NatIso.j (m-iso Id-Con C) ∘ ((NatIso.j e-iso ∘F ⟦ C ⟧₀) ∘ x))) lunit) 
            (trans 
             (cong (λ x → ⟦ ⌜ (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C) ⌝ ⟧₁ ∘ (NatIso.j (m-iso Id-Con C) ∘ x)) (∘runit {_} {_} {NatIso.j e-iso ∘F ⟦ C ⟧₀})) 
             (trans 
              (cong (λ x → x ∘ (NatIso.j (m-iso Id-Con C) ∘ (NatIso.j e-iso ∘F ⟦ C ⟧₀))) (fully-faithful-lem2-c {_} {_} {(NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C)})) 
              (trans 
               (sym (∘assoc {_} {_} {_} {_} {(NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ NatIso.i (m-iso Id-Con C)} {NatIso.j (m-iso Id-Con C)} {NatIso.j e-iso ∘F ⟦ C ⟧₀})) 
               (trans 
                (cong (λ x → (NatIso.i e-iso ∘F ⟦ C ⟧₀) ∘ x ∘ (NatIso.j e-iso ∘F ⟦ C ⟧₀)) (NatIso.iso-ax1 (m-iso Id-Con C))) 
                (trans 
                 (cong (λ x → x ∘ (NatIso.j e-iso ∘F ⟦ C ⟧₀)) (∘runit {_} {_} {NatIso.i e-iso ∘F ⟦ C ⟧₀})) 
                 (trans 
                  (sym (∘Fdist {_} {_} {_} {_} {NatIso.i e-iso} {NatIso.j e-iso})) 
                  (trans 
                   (cong (λ x → x ∘F ⟦ C ⟧₀) (NatIso.iso-ax1 e-iso)) 
                   (trans ∘Fid (sym ⟦⟧₁-id-eq))))))))))))))))))
