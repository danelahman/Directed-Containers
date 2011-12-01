{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers
open import DContainers renaming (_⇒_ to _⇒'_ ; _∘_ to _∘'_ ; ⇒-id to ⇒-id' ; ∘assoc to ∘assoc')
open import DContainerExt renaming (⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁' ; ⟦⟧₁-id-eq to ⟦⟧₁-id-eq')
open import Comonads renaming (_c∘_ to _c∘'_)
open import Functors

module Comonad2DContainerHelper where

open Containers
open Containers._⇒_
open Functor
open Comonad
open Functors._⇛_

abstract
  runit-lem : {C : Container} → {counit : ⟦ C ⟧₀ ⇛ Id-Fun} → {comult : ⟦ C ⟧₀ ⇛ (⟦ C ⟧₀ ⋆ ⟦ C ⟧₀)} → {runit : (⟦ C ⟧₀ F∘ counit) ∘ comult == ⇛-id {⟦ C ⟧₀}} → ⟦ (⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C (Id-Con)) ⌝) ◦ (C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝ ⟧₁ == ⟦ ⇒-id {C} ⟧₁
  runit-lem {C} {counit} {comult} {runit} = (trans 
   (⟦⟧₁-dist {_} {_} {_} {⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝} {(C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝}) 
   (trans 
    ((cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ x) (⟦⟧₁-dist {_} {_} {_} {(C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝)} {⌜ NatIso.j (m-iso C C ) ∘ comult ⌝})))
    (trans 
     (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ (⟦ C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝ ⟧₁ ∘ x)) (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C C) ∘ comult}) ) 
     (trans 
      (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ x) (sym (∘assoc {_} {_} {_} {_} {⟦ C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝ ⟧₁} {NatIso.j (m-iso C C)} {comult}))) 
      (trans 
        (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ (x ∘ comult)) (nat-eq (⟦ C C◦ ⌜ NatIso.j e-iso ∘ counit ⌝ ⟧₁ ∘ NatIso.j (m-iso C C)) (NatIso.j (m-iso C Id-Con) ∘ (⟦ C ⟧₀ F∘ ⟦ ⌜ NatIso.j e-iso ∘ counit ⌝ ⟧₁)) (ext (λ _ → cong2 _,_ refl refl)))) 
        (trans 
         (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ (NatIso.j (m-iso C Id-Con) ∘ (⟦ C ⟧₀ F∘ x) ∘ comult)) (fully-faithful-lem2-c {_} {_} {NatIso.j e-iso ∘ counit})) 
         (trans 
          (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ (NatIso.j (m-iso C Id-Con) ∘ x ∘ comult)) (F∘dist {⟦ C ⟧₀} {_} {_} {_} {NatIso.j e-iso} {counit})) 
          (trans 
           (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ x) (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso C Id-Con)} {(⟦ C ⟧₀ F∘ NatIso.j e-iso) ∘ (⟦ C ⟧₀ F∘ counit)} {comult})) 
           (trans 
            (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ (NatIso.j (m-iso C Id-Con) ∘ x)) (∘assoc {_} {_} {_} {_} {⟦ C ⟧₀ F∘ NatIso.j e-iso} {⟦ C ⟧₀ F∘ counit} {comult})) 
            (trans 
             (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ (NatIso.j (m-iso C Id-Con) ∘ ((⟦ C ⟧₀ F∘ NatIso.j e-iso) ∘  x))) runit) 
             (trans 
              (cong (λ x → ⟦ ⌜ (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con) ⌝ ⟧₁ ∘ (NatIso.j (m-iso C Id-Con) ∘ x)) (∘runit {_} {_} {(⟦ C ⟧₀ F∘ NatIso.j e-iso)})) 
              (trans 
               (cong (λ x → x ∘ (NatIso.j (m-iso C Id-Con) ∘ (⟦ C ⟧₀ F∘ NatIso.j e-iso))) (fully-faithful-lem2-c {_} {_} {(⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con)})) 
               (trans 
                (sym (∘assoc {_} {_} {_} {_} {(⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ NatIso.i (m-iso C Id-Con)} {NatIso.j (m-iso C Id-Con)} {⟦ C ⟧₀ F∘ NatIso.j e-iso})) 
                (trans 
                 (cong (λ x → (⟦ C ⟧₀ F∘ NatIso.i e-iso) ∘ x ∘ (⟦ C ⟧₀ F∘ NatIso.j e-iso)) (NatIso.iso-ax1 (m-iso C Id-Con))) 
                 (trans 
                  (cong (λ x → x ∘ (⟦ C ⟧₀ F∘ NatIso.j e-iso)) (∘runit {_} {_} {⟦ C ⟧₀ F∘ NatIso.i e-iso})) 
                  (trans 
                   (sym (F∘dist {_} {_} {_} {_} {NatIso.i e-iso} {NatIso.j e-iso})) 
                   (trans 
                    (cong (λ x → ⟦ C ⟧₀ F∘ x) (NatIso.iso-ax1 e-iso)) 
                    (trans F∘id (sym ⟦⟧₁-id-eq)))))))))))))))))))