{-# OPTIONS --type-in-type #-}

open import Utils 
open import Containers renaming (⌜_⌝ to ⌜_⌝' ; _⇒_ to _⇒'_ ; ⟦_⟧₀ to ⟦_⟧₀' ; ⟦_⟧₁ to ⟦_⟧₁')
open import DContainers renaming (⌈_⌉ to ⌈_⌉')
open import DContainerExt
open import Functors
open import Comonad2DContainer

open import Comonad2DContainer

module InterpretQuoteLem2 where

open Container
open DContainer renaming (Shape to Shape' ; Pos to Pos')

⌈⟦⟧₀⌉-lem : {C : DContainer} → ⌈ ⟦ C ⟧₀ , refl ⌉ == C
⌈⟦⟧₀⌉-lem {C} = 
  dcon-eq 
    ⌈ ⟦ C ⟧₀ , refl ⌉
    C
    refl 
    refl 
    (ext (λ s → ext (λ p → cong 
      (C ↓ s) 
      (stripsubst (Pos' C) p 
        (sym 
          (c2dc.comult'-ax1 
            (record { tr = λ {A} r → ∃.snd∃ r (o C); nat = λ {A} {B} f → refl }) 
            (record { tr = λ {A} r → ∃.fst∃ r , (λ p' → (C ↓ ∃.fst∃ r) p' , (λ p0 → ∃.snd∃ r ((C ⊕ p') p0))); nat = λ {A} {B} f → refl }) 
            (nat-eq 
              (record { tr = λ {X} z → (C ↓ ∃.fst∃ z) (o C) , (λ z' → ∃.snd∃ z ((C ⊕ o C) z')); nat = λ {X} {Y} h → refl }) 
              (record { tr = λ {X} z → z; nat = λ h → refl }) 
              (λ {A} → trans 
                (ext (λ s' → cong2 _,_ (ax1 C) (ext' (λ {a} {a'} x → cong (∃.snd∃ s') (trans (ax4 C a) x))))) 
                (ext (λ s' → refl)))) 
            (nat-eq 
              (record { tr = λ {X} z → ∃.fst∃ z , (λ z' → ∃.snd∃ z ((C ⊕ z') (o C))); nat = λ {X} {Y} h → refl }) 
              (record { tr = λ {X} z → z; nat = λ h → refl }) 
              (λ {A} → trans 
                (ext (λ s' → cong (_,_ (∃.fst∃ s')) (ext (λ a → cong (∃.snd∃ s') (ax3 C a))))) 
                (ext (λ x → refl)))) 
            (nat-eq 
              (record { tr = λ {X} z → ∃.fst∃ z , (λ z' → (C ↓ ∃.fst∃ z) z' , (λ p' → (C ↓ ∃.fst∃ z) ((C ⊕ z') p') , (λ p0 → ∃.snd∃ z ((C ⊕ (C ⊕ z') p') p0)))); nat = λ {X} {Y} h → refl }) 
              (record { tr = λ {X} z → ∃.fst∃ z , (λ z' → (C ↓ ∃.fst∃ z) z' , (λ p' → (C ↓ (C ↓ ∃.fst∃ z) z') p' , (λ p0 → ∃.snd∃ z ((C ⊕ z') ((C ⊕ p') p0))))); nat = λ {X} {Y} h → refl }) 
              (λ {A} → ext (λ s' → cong 
                (_,_ (∃.fst∃ s')) 
                (ext (λ a → cong 
                  (_,_ ((C ↓ ∃.fst∃ s') a)) 
                  (ext (λ a' → cong2 
                    _,_ 
                    (ax2 C) 
                    (ext' (λ {b} {b'} x → dcong 
                      (∃.snd∃ s') 
                      (trans 
                        (ax5 C a a' b) 
                        (cong 
                          (λ x' → (C ⊕ a) ((C ⊕ a') x')) 
                          (trans (stripsubst (Pos' C) b (ax2 C)) x)))))))))))))))))) 
    refl 
    (iext (λ s → ext (λ p → ext' (λ {p'} {p''} x → cong2 
      (λ x y → (C ⊕ x) y) 
      (stripsubst (Pos' C) p 
        (sym (c2dc.comult'-ax1 
          (record { tr = λ {A} r → ∃.snd∃ r (o C); nat = λ {A} {B} f → refl }) 
          (record { tr = λ {A} r → ∃.fst∃ r , (λ p0 → (C ↓ ∃.fst∃ r) p0 , (λ p1 → ∃.snd∃ r ((C ⊕ p0) p1))); nat = λ {A} {B} f → refl }) 
          (nat-eq 
            (record { tr = λ {X} z → (C ↓ ∃.fst∃ z) (o C) , (λ z' → ∃.snd∃ z ((C ⊕ o C) z')); nat = λ {X} {Y} h → refl }) 
            (record { tr = λ {X} z → z; nat = λ h → refl }) 
            (λ {A} → trans (ext (λ s' → cong2 _,_ (ax1 C) (ext' (λ {a} {a'} x' → cong (∃.snd∃ s') (trans (ax4 C a) x'))))) (ext (λ s' → refl)))) 
          (nat-eq 
            (record { tr = λ {X} z → ∃.fst∃ z , (λ z' → ∃.snd∃ z ((C ⊕ z') (o C))); nat = λ {X} {Y} h → refl }) 
            (record { tr = λ {X} z → z; nat = λ h → refl }) 
            (λ {A} → trans (ext (λ s' → cong (_,_ (∃.fst∃ s')) (ext (λ a → cong (∃.snd∃ s') (ax3 C a))))) (ext (λ x' → refl)))) 
          (nat-eq 
            (record { tr = λ {X} z → ∃.fst∃ z , (λ z' → (C ↓ ∃.fst∃ z) z' , (λ p0 → (C ↓ ∃.fst∃ z) ((C ⊕ z') p0) , (λ p1 → ∃.snd∃ z ((C ⊕ (C ⊕ z') p0) p1)))); nat = λ {X} {Y} h → refl }) 
            (record { tr = λ {X} z → ∃.fst∃ z , (λ z' → (C ↓ ∃.fst∃ z) z' , (λ p0 → (C ↓ (C ↓ ∃.fst∃ z) z') p0 , (λ p1 → ∃.snd∃ z ((C ⊕ z') ((C ⊕ p0) p1))))); nat = λ {X} {Y} h → refl }) 
            (λ {A} → ext (λ s' → cong 
              (_,_ (∃.fst∃ s')) 
              (ext (λ a → cong 
                (_,_ ((C ↓ ∃.fst∃ s') a)) 
                (ext (λ a' → cong2 
                  _,_ 
                  (ax2 C) 
                  (ext' (λ {b} {b'} x' → dcong 
                    (∃.snd∃ s') 
                    (trans 
                      (ax5 C a a' b) 
                      (cong (λ x0 → (C ⊕ a) ((C ⊕ a') x0)) (trans (stripsubst (Pos' C) b (ax2 C)) x'))))))))))))))) 
      x))))