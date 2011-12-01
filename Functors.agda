{-# OPTIONS --type-in-type #-}

open import Utils 

module Functors  where

record Functor : Set where
  constructor Functor⋆
  field omap : Set → Set
        fmap : ∀ {A B} → (A → B) → (omap A → omap B)
        id-ax : ∀ {A} → fmap (identity {A}) == identity {omap A}
        comp-ax : ∀ {A B C} → {f : A → B} → {g : B → C} → fmap (g · f) == (fmap g) · (fmap f)

open Functor

functor-eq : (F F' : Functor) → omap F == omap F' → (∀ {A B} → fmap F {A} {B} == fmap F' {A} {B}) → F == F'
functor-eq F F' p q = cong4
  {Set → Set}
  {λ omap → ∀ {A B} → (A → B) → (omap A → omap B)}
  {λ omap fmap → ∀ {A} → fmap (identity {A}) == identity {omap A}}
  {λ omap fmap _ → ∀ {A B C} → {f : A → B} → {g : B → C} → fmap (g · f) == (fmap g) · (fmap f)}
  {λ _ _ _ _ → Functor}
  (λ a b c d → record {omap = a ; fmap = b ; id-ax = c ; comp-ax = d}) 
  p 
  (iext (λ _ → iext (λ _ → q))) 
  (iext (λ a → fixtypes (cong' refl (ext (λ a' → cong2 (λ x y → (x → y)) (cong' refl refl p) (cong' refl refl p))) q) (ext' (λ x → x)))) 
  ((iext (λ a → iext (λ a' → iext (λ a0 → iext (λ a1 → iext (λ a2 → fixtypes (cong' refl (ext (λ a3 → cong2 (λ x y → x → y) (cong' (refl {a = a}) refl p) (cong' (refl {a = a0}) refl p))) q) (ext' (λ {a3} {a4} x → cong' (cong' x (ext' (λ x' → cong' (refl {a = a'}) refl p)) (cong' (refl {a = a1}) (ext (λ _ → cong2 (λ x' y → x' → y) (cong' (refl {a = a}) refl p) (cong' (refl {a = a'}) refl p))) q)) (ext' (λ _ → cong' (refl {a = a0}) refl p)) (cong' (refl {a = a2}) (ext (λ _ → cong2 (λ x' y → x' → y) (cong' (refl {a = a'}) refl p) (cong' (refl {a = a0}) refl p))) q))))))))))

Id-Fun : Functor
Id-Fun = record {omap = λ X → X ; fmap = λ f → f ; id-ax = refl ; comp-ax = refl}

_+F_ : Functor → Functor → Functor
F +F F' = record {omap = λ X → (omap F X + omap F' X) ; fmap = fmap' ; id-ax = ext (λ x → id-ax' x) ; comp-ax = ext (λ x → comp-ax' x)} module coprod where
  fmap' : {A B : Set} → (A → B) → omap F A + omap F' A → omap F B + omap F' B
  fmap' f (inl x) = inl (fmap F f x)
  fmap' f (inr x) = inr (fmap F' f x)
  id-ax' : {A : Set} → (x : omap F A + omap F' A) → fmap' identity x == x
  id-ax' {A} (inl x) = cong inl (cong' refl refl {fmap F identity} {identity} (id-ax F))
  id-ax' {A} (inr x) = cong inr (cong' refl refl {fmap F' identity} {identity} (id-ax F'))
  comp-ax' : {A B C : Set} → {f : A → B} → {g : B → C} → (x : omap F A + omap F' A) → fmap' (g · f) x == fmap' g (fmap' f x)
  comp-ax' {A} {B} {C} {f} {g} (inl x) = cong inl (cong' refl refl {fmap F (g · f)} {(fmap F g) · (fmap F f)} (comp-ax F))
  comp-ax' {A} {B} {C} {f} {g} (inr x) = cong inr (cong' refl refl {fmap F' (g · f)} {(fmap F' g) · (fmap F' f)} (comp-ax F'))

_⋆_ : Functor → Functor → Functor
F ⋆ F' = record {omap = λ X → omap F (omap F' X) ; fmap = λ f → fmap F (fmap F' f) ; id-ax = trans (cong (fmap F) (id-ax F')) (id-ax F) ; comp-ax = trans (cong (fmap F) (comp-ax F')) (comp-ax F) }

infixl 60 _⋆_

record _⇛_ (F F' : Functor) : Set where
  field tr : ∀ {X} → omap F X → omap F' X
        nat : ∀ {X Y} → (h : X → Y) → fmap F' h · tr {X} == tr {Y} · fmap F h

open _⇛_

abstract
  nat-eq : {F F' : Functor} → (α β : F ⇛ F') → (∀ {X} → tr α {X} == tr β {X}) → α == β
  nat-eq {F} {F'} α β p = cong2 
    {∀ {X} → omap F X → omap F' X}
    {λ tr → ∀ {X Y} → (h : X → Y) → fmap F' h · tr {X} == tr {Y} · fmap F h}
    {λ _ _ → F ⇛ F'}
    (λ x y → record {tr = x ; nat = y}) 
    (iext (λ _ → p)) 
    (iext (λ X → iext (λ Y → ext (λ h → fixtypes (cong (_·_ (fmap F' h)) p) (cong (λ z → z · fmap F h) p)))))

⇛-id : {F : Functor} → F ⇛ F
⇛-id = record { tr = λ x → x; nat = λ h → refl }

_∘_ : {F F' F'' : Functor} → F' ⇛ F'' → F ⇛ F' → F ⇛ F''
_∘_ {F} {F'} {F''} f g = record {tr = tr f · tr g ; nat = λ {X} {Y} h → trans (sym (·assoc {_} {_} {_} {_} {tr g} {tr f} {fmap F'' h})) (trans (cong (λ x → x · tr g {X}) (nat f {X} {Y} h)) (trans (·assoc {_} {_} {_} {_} {tr g} {fmap F' h} {tr f}) (trans (cong (_·_ (tr f {Y})) (nat g {X} {Y} h)) (sym (·assoc {_} {_} {_} {_} {fmap F h} {tr g} {tr f})))))}

abstract
  ∘assoc : {F F' F'' F''' : Functor} → {f : F'' ⇛ F'''} → {g : F' ⇛ F''} → {h : F ⇛ F'} → f ∘ g ∘ h == f ∘ (g ∘ h)
  ∘assoc {F} {F'} {F''} {F'''} {f} {g} {h} = nat-eq _ _ (·assoc {_} {_} {_} {_} {tr h} {tr g} {tr f})

  ∘lunit : {F F' : Functor} → {f : F ⇛ F'} → ⇛-id ∘ f == f
  ∘lunit = nat-eq _ _ refl

  ∘runit : {F F' : Functor} → {f : F ⇛ F'} → f ∘ ⇛-id == f
  ∘runit = nat-eq _ _ refl

infixl 60 _∘_


_F∘_ : {F G : Functor} → (H : Functor) → (α : F ⇛ G) → H ⋆ F ⇛ H ⋆ G
(Functor⋆ omap fmap id-ax comp-ax) F∘ α = record { tr = fmap (tr α) ; nat = λ h → trans (sym comp-ax) (trans (cong fmap (nat α h)) comp-ax) }

_∘F_ : {F G : Functor} → (α : F ⇛ G) → (H : Functor) → F ⋆ H ⇛ G ⋆ H
_∘F_ α (Functor⋆ omap fmap id-ax comp-ax) = record { tr = tr α; nat = λ h → nat α (fmap h) }

abstract
  F∘dist : {F F' F'' F''' : Functor} → {f : F'' ⇛ F'''} → {g : F' ⇛ F''} → (F F∘ (f ∘ g)) == (F F∘ f) ∘ (F F∘ g)
  F∘dist {F} {F'} {F''} {F'''} {f} {g} = nat-eq _ _ (comp-ax F)

  ∘Fdist : {F F' F'' F''' : Functor} → {f : F'' ⇛ F'''} → {g : F' ⇛ F''} → ((f ∘ g) ∘F F) == (f ∘F F) ∘ (g ∘F F)
  ∘Fdist = nat-eq _ _ refl

  F∘id : {F : Functor} → (_F∘_ {Id-Fun} {Id-Fun} F ⇛-id) == ⇛-id {F ⋆ Id-Fun}
  F∘id {F} = nat-eq _ _ (id-ax F)

  ∘Fid : {F : Functor} → (_∘F_ {Id-Fun} {Id-Fun} ⇛-id F) == ⇛-id {Id-Fun ⋆ F}
  ∘Fid {F} = nat-eq _ _ refl

record NatIso (F F' : Functor) : Set where
  constructor _≅_
  field i : F ⇛ F'
        j : F' ⇛ F
        iso-ax1 : i ∘ j == ⇛-id {F'}
        iso-ax2 : j ∘ i == ⇛-id {F}
