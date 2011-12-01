{-# OPTIONS --type-in-type #-}

open import Utils 
open import DContainers renaming (_∘_ to _∘'_)
open import Functors

module Comonads  where

open Functor
open _⇛_

record Comonad : Set where
  constructor CM
  field Fun : Functor
        counit : Fun ⇛ Id-Fun
        comult : Fun ⇛ (Fun ⋆ Fun)
        lunit-ax : (counit ∘F Fun) ∘ comult == ⇛-id {Fun}
        runit-ax : (Fun F∘ counit) ∘ comult == ⇛-id {Fun}
        assoc-ax : (comult ∘F Fun) ∘ comult == (Fun F∘ comult) ∘ comult
   
open Comonad

comonad-eq : (CM CM' : Comonad) → Fun CM == Fun CM' → counit CM == counit CM' → comult CM == comult CM' → CM == CM'
comonad-eq C C' p q r = cong6 
  {Functor}
  {λ Fun → Fun ⇛ Id-Fun}
  {λ Fun _ → Fun ⇛ (Fun ⋆ Fun)}
  {λ Fun counit comult → (counit ∘F Fun) ∘ comult == ⇛-id {Fun}}
  {λ Fun counit comult _ → (Fun F∘ counit) ∘ comult == ⇛-id {Fun}}
  {λ Fun counit comult _ _ → (comult ∘F Fun) ∘ comult == (Fun F∘ comult) ∘ comult}
  {λ _ _ _ _ _ _ → Comonad}
  (λ a b c d e f → record {Fun = a ; counit = b ; comult = c ; lunit-ax = d ; runit-ax = e; assoc-ax = f}) 
  p 
  q 
  r 
  (fixtypesX (cong3'' {Functor} {λ f → f ⇛ Id-Fun} {λ f → f ⇛ Id-Fun} refl refl {λ x y z → x ⇛ Id-Fun ⋆ x} {λ x y z → x ⇛ Id-Fun ⋆ x} refl {λ x y z → (y ∘F x) ∘ z} {λ x y z → (y ∘F x) ∘ z} refl p q r) (icong' {Functor} {Functor} {Fun C} {Fun C'} p {λ f → f ⇛ f} {λ f → f ⇛ f} refl {⇛-id} {⇛-id} refl)) 
  (fixtypesX (cong3'' {Functor} {λ f → f ⇛ Id-Fun} {λ f → f ⇛ Id-Fun} refl refl {λ x y z → x ⇛ x ⋆ Id-Fun} {λ x y z → x ⇛ x ⋆ Id-Fun} refl {λ x y z → (x F∘ y) ∘ z} {λ x y z → (x F∘ y) ∘ z} refl p q r) (icong' {Functor} {Functor} {Fun C} {Fun C'} p {λ f → f ⇛ f} {λ f → f ⇛ f} refl {⇛-id} {⇛-id} refl))
  (fixtypesX (cong3'' {Functor} {λ f → f ⇛ f ⋆ f} {λ f → f ⇛ f ⋆ f} refl refl {λ x y z → x ⇛ x ⋆ x ⋆ x} {λ x y z → x ⇛ x ⋆ x ⋆ x} refl {λ x y z → (y ∘F x) ∘ z} {λ x y z → (y ∘F x) ∘ z} refl p r r) (cong3'' {Functor} {λ f → f ⇛ f ⋆ f} {λ f → f ⇛ f ⋆ f} refl refl {λ x y z → x ⇛ x ⋆ (x ⋆ x)} {λ x y z → x ⇛ x ⋆ (x ⋆ x)} refl {λ x y z → (x F∘ y) ∘ z} {λ x y z → (x F∘ y) ∘ z} refl p r r))

Id-Comonad : Comonad
Id-Comonad = CM Id-Fun ⇛-id ⇛-id refl refl refl

record _⇨_ (C C' : Comonad) : Set where
  field tr' : Fun C ⇛ Fun C'
        cu : counit C' ∘ tr' == counit C
        cm : comult C' ∘ tr' == (Fun C' F∘ tr') ∘ (tr' ∘F Fun C) ∘ comult C
open _⇨_

⇨-id : {C : Comonad} → C ⇨ C
⇨-id {C} = record { tr' = record { tr = λ {X} x → x; nat = λ {X} {Y} h → refl } ; cu = nat-eq _ _ refl; cm = nat-eq _ _ (trans (·runit) (sym (trans (·assoc {_} {_} {_} {_} {tr (comult C)} {λ x → x} {fmap (Fun C) (λ x → x)}) (trans (cong (λ x → x · ((λ x → x) · tr (comult C))) (id-ax (Fun C))) (trans (·lunit) refl)))))}

_c∘_ : {C C' C'' : Comonad} → (f : C ⇨ C') → (g : C' ⇨ C'') → C ⇨ C''
_c∘_ {C} {C'} {C''} f g = record { tr' = record {tr = tr'' ; nat = nat''} ; cu = nat-eq _ _ (λ {X} → cu' {X}) ; cm = nat-eq _ _ (λ {X} → cm' {X}) } where
  tr'' : {X : Set} → omap (Fun C) X → omap (Fun C'') X
  tr'' c = tr (tr' g) (tr (tr' f) c)
  nat'' : {X Y : Set} (h : X → Y) → fmap (Fun C'') h · tr'' == tr'' · fmap (Fun C) h
  nat'' {X} {Y} h = ext λ x → trans (cong' refl refl (nat (tr' g) h)) (cong (tr (tr' g)) (cong' refl refl (nat (tr' f) h) ))
  cu' : {X : Set} → tr (counit C'') · tr'' == tr (counit C)
  cu' {X} = trans (cong (λ x → x · tr (tr' f)) (icong' refl refl (cong tr (cu g)))) (icong' refl refl (cong tr (cu f)))
  cm' : {X : Set} → tr (comult C'') · tr'' == fmap (Fun C'') tr'' · tr'' · tr (comult C)
  cm' {X} = trans (cong (λ x → x · (tr (tr' f))) (icong' refl refl (cong tr (cm g)))) (trans (cong (λ x → fmap (Fun C'') (tr (tr' g)) · tr (tr' g) · x) (icong' refl refl (cong tr (cm f)))) (trans (cong (λ x → fmap (Fun C'') (tr (tr' g)) · x · tr (tr' f) · tr (comult C)) (sym (nat (tr' g) (tr (tr' f))))) (sym (cong (λ x → x · tr'' · tr (comult C)) (comp-ax (Fun C'') {_} {_} {_} {tr (tr' f)} {tr (tr' g)})))))

comonad-morph-eq : {C C' : Comonad} → (f g : C ⇨ C') → (∀ X → tr (tr' f) {X} == tr (tr' g) {X}) → f == g
comonad-morph-eq {C} {C'} f g p = cong3 
  {Fun C ⇛ Fun C'} 
  {λ tr' → counit C' ∘ tr' == counit C} 
  {λ tr' _ → comult C' ∘ tr' == (Fun C' F∘ tr') ∘ (tr' ∘F Fun C) ∘ comult C} 
  {λ _ _ _ → C ⇨ C'} 
  (λ h cu' cm' → record {tr' = h ; cu = cu' ; cm = cm'}) 
  (nat-eq _ _ (p _)) 
  (fixtypes (nat-eq _ _ (cong (λ x → tr (counit C') · x) (ext (λ a → cong (λ x → x a) (p _))))) refl) 
  (fixtypes (nat-eq _ _ (cong (λ x → tr (comult C') · x) (ext (λ a → cong (λ x → x a) (p _))))) (nat-eq _ _ (ext (λ a → cong2 (fmap (Fun C')) (ext (λ a → cong (λ x → x a) (p _))) (cong (λ x → x (tr (comult C) a)) (p _))))))

record ComonadIso (CM CM' : Comonad) : Set where
  constructor _≅_
  field i : CM ⇨ CM'
        j : CM' ⇨ CM
        iso-ax1 : ∀ {X} → tr (tr' i) · tr (tr' j) {X} == identity {omap (Fun CM') X}
        iso-ax2 : ∀ {X} → tr (tr' j) · tr (tr' i) {X} == identity {omap (Fun CM) X}