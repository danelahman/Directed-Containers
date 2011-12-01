{-# OPTIONS --type-in-type #-}

open import Utils 
open import Functors

module Containers  where

record Container : Set where
  constructor _◁_
  field Shape : Set
        Pos : Shape → Set

open Container

Id-Con : Container
Id-Con = ⊤ ◁ (λ _ → ⊤)

open Functor

_[_] : Container → Container → Container
(S₁ ◁ P₁) [ S₀ ◁ P₀ ] = ∃ S₁ (λ s → (P₁ s → S₀)) ◁ λ s → ∃ (P₁ (∃.fst∃ s)) (λ p → P₀ (∃.snd∃ s p))

_X'_ : Container → Container → Container
(S ◁ P) X' (Q ◁ R) = (S × Q) ◁ f where
        f : (S × Q) → Set
        f (s , q) = (P s) + (R q)

_+'_ : Container → Container → Container
(S ◁ P) +' (Q ◁ R) = (S + Q) ◁ f where
        f : (S + Q) → Set 
        f (inl s) = P s
        f (inr q) = R q

⟦_⟧₀ : Container → Functor
⟦ S ◁ P ⟧₀ = record { omap = λ X → ∃ S (λ s → P s → X); fmap = fmap'; id-ax = refl; comp-ax = refl } module fmap' where
  fmap' : {S : Set} → {P : S → Set} → {A B : Set} → (A → B) → ∃ S (λ s → P s → A) → ∃ S (λ s → P s → B)
  fmap' f (s , p) = s , (f · p)



record _⇒_ (C C' : Container) : Set where
  constructor _◁'_
  field sf : Shape C → Shape C'
        pf : (s : Shape C) → Pos C' (sf s) → Pos C s

open _⇒_
open _⇛_

abstract
  ⇒-pf : {C C' : Container} → {f g : C ⇒ C'} → {s s' : Shape C} → {p : Pos C' (sf f s)} → {p' : Pos C' (sf g s')} → f == g →  s == s' → p == p' → pf f s p == pf g s' p'
  ⇒-pf refl refl refl = refl

ρ-iso : (C : Container) → C [ Id-Con ] ⇒ C
ρ-iso (S ◁ P) = (λ s → ∃.fst∃ s) ◁' λ s p → p , tt

λ-iso : (C : Container) → Id-Con [ C ] ⇒ C
λ-iso (S ◁ P) = (λ s → ∃.snd∃ s tt) ◁' λ s p → tt , p

_◦_ : {C C' C'' : Container} → (g : C' ⇒ C'') → (f : C ⇒ C') → C ⇒ C''
_◦_ {C} {C'} {C''} (sf' ◁' pf') (sf ◁' pf) = sf' · sf ◁' λ s p → pf s (pf' (sf s) p)

infixl 60 _◦_

_C◦_ : {C' C'' : Container} → (C : Container) → (α : C' ⇒ C'') → C [ C' ] ⇒ C [ C'' ]
(S ◁ P) C◦ (sf ◁' pf) = (λ s → (∃.fst∃ s) , (sf · (∃.snd∃ s))) ◁' (λ s p → (∃.fst∃ p) , (pf (∃.snd∃ s (∃.fst∃ p)) (∃.snd∃ p)))

_◦C_ : {C' C'' : Container} → (α : C' ⇒ C'') → (C : Container) → C' [ C ] ⇒ C'' [ C ]
(sf ◁' pf) ◦C (Shape ◁ Pos) = (λ s → (sf (∃.fst∃ s)) , ((∃.snd∃ s) · pf (∃.fst∃ s))) ◁' λ s p → (pf (∃.fst∃ s) (∃.fst∃ p)) , (∃.snd∃ p)

⇒-id : {C : Container} → C ⇒ C
⇒-id = (λ s → s) ◁' λ s p → p

⇒-cong : {C D E : Container} → (C ⇒ D) → (C [ E ] ⇒ D [ E ])
⇒-cong morph = record {sf = λ s → (sf morph (∃.fst∃ s)) , (λ p → ∃.snd∃ s (pf morph (∃.fst∃ s) p)) ; pf = λ s p → (pf morph (∃.fst∃ s) (∃.fst∃ p)) , (∃.snd∃ p)}

⇒-cong' : {C D E : Container} → (C ⇒ D) → (E [ C ] ⇒ E [ D ])
⇒-cong' morph = record {sf = λ s → (∃.fst∃ s) , (λ p → sf morph (∃.snd∃ s p)) ; pf = λ s p → (∃.fst∃ p) , pf morph (∃.snd∃ s (∃.fst∃ p)) (∃.snd∃ p)}

α-iso1 : (C C' C'' : Container) → (C [ C' ]) [ C'' ] ⇒ C [ C' [ C'' ] ]
α-iso1 (Shape ◁ Pos) (Shape' ◁ Pos') (Shape'' ◁ Pos'') = (λ s → (∃.fst∃ (∃.fst∃ s)) , (λ p → ∃.snd∃ (∃.fst∃ s) p , λ p' → ∃.snd∃ s (p , p'))) ◁' λ s p → ((∃.fst∃ p) , (∃.fst∃ (∃.snd∃ p))) , (∃.snd∃ (∃.snd∃ p))

α-iso2 : (C C' C'' : Container) → C [ C' [ C'' ] ] ⇒ (C [ C' ]) [ C'' ]
α-iso2 (Shape ◁ Pos) (Shape' ◁ Pos') (Shape'' ◁ Pos'') = (λ s → ((∃.fst∃ s) , (λ p → ∃.fst∃ ((∃.snd∃ s) p))) , λ p' → ∃.snd∃ (∃.snd∃ s (∃.fst∃ p')) (∃.snd∃ p')) ◁' (λ s p → (∃.fst∃ (∃.fst∃ p)) , ((∃.snd∃ (∃.fst∃ p)) , (∃.snd∃ p)))

⟦_⟧₁ : {C C' : Container} → C ⇒ C' → ⟦ C ⟧₀ ⇛ ⟦ C' ⟧₀ 
⟦_⟧₁ {S ◁ P} {S' ◁ P'} (sf ◁' pf) = record {tr = tr' ; nat = nat'} where
 tr' : {X : Set} → ∃ S (λ s → P s → X) → ∃ S' (λ s → P' s → X)
 tr' (s , f) = (sf s) , (f · pf s)
 abstract
   nat' : {X Y : Set} (h : X → Y) → fmap ⟦ S' ◁ P' ⟧₀  h · tr' == tr' · fmap ⟦ S ◁ P ⟧₀ h
   nat' h = refl

abstract
  ⟦⟧₁-dist : {C C' C'' : Container} → {g : C' ⇒ C''} → {f : C ⇒ C'} → ⟦ g ◦ f ⟧₁ == ⟦ g ⟧₁ ∘ ⟦ f ⟧₁
  ⟦⟧₁-dist = nat-eq _ _ refl

  ⟦⟧₁-id-eq : {C : Container} → ⟦ ⇒-id {C} ⟧₁ == ⇛-id {⟦ C ⟧₀}
  ⟦⟧₁-id-eq = nat-eq _ _ refl



⌜_⌝ : {C C' : Container} → ⟦ C ⟧₀ ⇛ ⟦ C' ⟧₀ → C ⇒ C'
⌜ Nt ⌝ = (λ s → ∃.fst∃ (tr Nt (s , identity))) ◁' λ s p → ∃.snd∃ (tr Nt (s , identity)) p

abstract

  fully-faithful-lem1-c : {C C' : Container} → {f : C ⇒ C'} → ⌜ ⟦ f ⟧₁ ⌝ == f
  fully-faithful-lem1-c = refl

  fully-faithful-lem2-c : {C C' : Container} → {f : ⟦ C ⟧₀ ⇛ ⟦ C' ⟧₀} → ⟦ ⌜ f ⌝ ⟧₁ == f
  fully-faithful-lem2-c {C} {C'} {f} = nat-eq _ _ (ext (λ s → cong' refl refl (nat f (∃.snd∃ s))))

  fully-faithful-lem3-c : {C C' : Container} → {f g : C ⇒ C'} → ⟦ f ⟧₁ == ⟦ g ⟧₁ → f == g
  fully-faithful-lem3-c p = trans (sym (fully-faithful-lem1-c)) (trans (cong ⌜_⌝ p) (fully-faithful-lem1-c))

  fully-faithful-lem4-c : {C C' : Container} → {f g : ⟦ C ⟧₀ ⇛ ⟦ C' ⟧₀} → ⌜ f ⌝ == ⌜ g ⌝ → f == g
  fully-faithful-lem4-c {C} {C'} {f} {g} p = nat-eq f g (trans (icong' refl refl (sym (cong tr (fully-faithful-lem2-c {C} {C'} {f})))) (trans (cong (λ x → tr ⟦ x ⟧₁) p) (icong' refl refl (cong tr {⟦ ⌜ g ⌝ ⟧₁} {g} (fully-faithful-lem2-c {C} {C'} {g})))))

e-iso : NatIso ⟦ Id-Con ⟧₀ Id-Fun
e-iso = _≅_ (record {tr = λ x → ∃.snd∃ x tt ; nat = λ h → refl}) (record {tr = λ x → tt , λ x' → x ; nat = λ h → refl}) refl refl

m-iso : (C C' : Container) → NatIso (⟦ (C [ C' ]) ⟧₀) (⟦ C ⟧₀ ⋆ ⟦ C' ⟧₀)
m-iso C C' = _≅_ (record {tr = λ s → (∃.fst∃ (∃.fst∃ s)) , (λ p → (∃.snd∃ (∃.fst∃ s) p) , (λ p' → ∃.snd∃ s (p , p'))) ; nat = λ h → refl }) (record {tr = λ s → ((∃.fst∃ s) , (λ p → ∃.fst∃ (∃.snd∃ s p))) , λ p → ∃.snd∃ (∃.snd∃ s (∃.fst∃ p)) (∃.snd∃ p) ; nat = λ h → refl}) refl refl