{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers
open import DContainers renaming (_⇒_ to _⇒'_ ; _∘_ to _∘'_ ; ∘assoc to ∘assoc')
open import DContainerExt renaming (⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁')
open import Comonads renaming (_c∘_ to _c∘'_)
open import Functors

module Comonad2DContainerHelper3 where

open Container
open Containers._⇒_
open Functor
open Comonad
open Functors._⇛_

abstract
  assoc-lem' : {C : Container} → {counit : ⟦ C ⟧₀ ⇛ Id-Fun} → {comult : ⟦ C ⟧₀ ⇛ (⟦ C ⟧₀ ⋆ ⟦ C ⟧₀)} → {assoc : (comult ∘F ⟦ C ⟧₀) ∘ comult == (⟦ C ⟧₀ F∘ comult) ∘ comult} → (NatIso.j (m-iso C (C [ C ]) ) ∘ (⟦ C ⟧₀ F∘ NatIso.j (m-iso C C))) == ⟦ α-iso1 C C C ⟧₁ ∘ NatIso.j (m-iso (C [ C ]) C ) ∘ (NatIso.j (m-iso C C) ∘F ⟦ C ⟧₀)
  assoc-lem' {C} {counit} {comult} {assoc} = nat-eq _ _ (ext (λ s → cong2 _,_ refl (ext (λ p → refl))))


abstract
  assoc-lem : {C : Container} → {counit : ⟦ C ⟧₀ ⇛ Id-Fun} → {comult : ⟦ C ⟧₀ ⇛ (⟦ C ⟧₀ ⋆ ⟦ C ⟧₀)} → {assoc : (comult ∘F ⟦ C ⟧₀) ∘ comult == (⟦ C ⟧₀ F∘ comult) ∘ comult} → ⟦ (C C◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝ ⟧₁ == ⟦ (α-iso1 C C C) ◦ (⌜ NatIso.j (m-iso C C ) ∘ comult ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝ ⟧₁
  assoc-lem {C} {counit} {comult} {assoc} = 
   trans 
   (⟦⟧₁-dist {_} {_} {_} {C C◦ ⌜ NatIso.j (m-iso C C ) ∘ comult ⌝} {⌜ NatIso.j (m-iso C C ) ∘ comult ⌝}) 
   (trans 
    (cong (λ x → ⟦ C C◦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ⟧₁ ∘ x) (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C C) ∘ comult})) 
    (trans 
     (sym (∘assoc {_} {_} {_} {_} {⟦ C C◦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ⟧₁} {NatIso.j (m-iso C C)} {comult})) 
     (trans 
      (cong (λ x → x ∘ comult) (nat-eq (⟦ C C◦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ⟧₁ ∘ NatIso.j (m-iso C C)) (NatIso.j (m-iso C (C [ C ])) ∘ (⟦ C ⟧₀ F∘ ⟦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ⟧₁)) (ext (λ _ → cong2 _,_ refl refl)))) 
       (trans 
        (cong (λ x → NatIso.j (m-iso C (C [ C ])) ∘ (⟦ C ⟧₀ F∘ x) ∘ comult) (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C C) ∘ comult})) 
        (trans 
         (cong (λ x → NatIso.j (m-iso C (C [ C ])) ∘ x ∘ comult) (F∘dist {⟦ C ⟧₀} {_} {_} {_} {NatIso.j (m-iso C C)} {comult})) 
         (trans 
          (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso C (C [ C ]))} {(⟦ C ⟧₀ F∘ NatIso.j (m-iso C C)) ∘ (⟦ C ⟧₀ F∘ comult)} {comult}) 
          (sym 
           (trans 
            (⟦⟧₁-dist {_} {_} {_} {α-iso1 C C C} {(⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ◦C C) ◦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝}) 
            (trans 
             (cong (λ x → ⟦ α-iso1 C C C ⟧₁ ∘ x) (⟦⟧₁-dist {_} {_} {_} {(⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ◦C C)} {⌜ NatIso.j (m-iso C C) ∘ comult ⌝})) 
             (trans 
              (cong (λ x → ⟦ α-iso1 C C C ⟧₁ ∘ (⟦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ◦C C ⟧₁ ∘ x)) (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C C) ∘ comult})) 
              (trans 
               (cong (λ x → ⟦ α-iso1 C C C ⟧₁ ∘ x) (sym (∘assoc {_} {_} {_} {_} {⟦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ◦C C ⟧₁} {NatIso.j (m-iso C C)} {comult}))) 
               (trans 
                (cong (λ x → ⟦ α-iso1 C C C ⟧₁ ∘ (x ∘ comult)) (nat-eq (⟦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ◦C C ⟧₁ ∘ NatIso.j (m-iso C C)) (NatIso.j (m-iso (C [ C ]) C) ∘ (⟦ ⌜ NatIso.j (m-iso C C) ∘ comult ⌝ ⟧₁ ∘F ⟦ C ⟧₀)) (ext (λ _ → cong2 _,_ refl refl)))) 
                (trans 
                 (cong (λ x → ⟦ α-iso1 C C C ⟧₁ ∘ (NatIso.j (m-iso (C [ C ]) C) ∘ (x ∘F ⟦ C ⟧₀) ∘ comult)) (fully-faithful-lem2-c {_} {_} {NatIso.j (m-iso C C) ∘ comult})) 
                 (trans
                  (cong (λ x → ⟦ α-iso1 C C C ⟧₁ ∘ (NatIso.j (m-iso (C [ C ]) C) ∘ x ∘ comult)) (∘Fdist {⟦ C ⟧₀} {_} {_} {_} {NatIso.j (m-iso C C)} {comult})) 
                  (trans 
                   (sym (∘assoc {_} {_} {_} {_} {⟦ α-iso1 C C C ⟧₁} {NatIso.j (m-iso (C [ C ]) C) ∘ ((NatIso.j (m-iso C C) ∘F ⟦ C ⟧₀) ∘ (comult ∘F ⟦ C ⟧₀))} {comult})) 
                   (trans 
                    (cong (λ x → x ∘ comult) (sym (∘assoc {_} {_} {_} {_} {⟦ α-iso1 C C C ⟧₁} {NatIso.j (m-iso (C [ C ]) C)} {(NatIso.j (m-iso C C) ∘F ⟦ C ⟧₀) ∘ (comult ∘F ⟦ C ⟧₀)}))) 
                    (trans 
                     (cong (λ x → x ∘ comult) (sym (∘assoc {_} {_} {_} {_} { ⟦ α-iso1 C C C ⟧₁ ∘ NatIso.j (m-iso (C [ C ]) C)} {NatIso.j (m-iso C C) ∘F ⟦ C ⟧₀} {comult ∘F ⟦ C ⟧₀}))) 
                     (trans 
                      (cong (λ x → x ∘ (comult ∘F ⟦ C ⟧₀) ∘ comult) (sym (assoc-lem' {C} {counit} {comult} {assoc}))) 
                      (trans 
                       (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso C (C [ C ])) ∘ (⟦ C ⟧₀ F∘ NatIso.j (m-iso C C))} {comult ∘F ⟦ C ⟧₀} {comult}) 
                       (trans 
                        (cong (λ x → NatIso.j (m-iso C (C [ C ])) ∘ (⟦ C ⟧₀ F∘ NatIso.j (m-iso C C)) ∘ x) assoc) 
                        (trans 
                         (∘assoc {_} {_} {_} {_} {NatIso.j (m-iso C (C [ C ]))} {(⟦ C ⟧₀ F∘ NatIso.j (m-iso C C))} {(⟦ C ⟧₀ F∘ comult) ∘ comult}) 
                         (cong (λ x → NatIso.j (m-iso C (C [ C ])) ∘ x) (sym (∘assoc {_} {_} {_} {_} {⟦ C ⟧₀ F∘ NatIso.j (m-iso C C)} {⟦ C ⟧₀ F∘ comult} {comult}))))))))))))))))))))))))