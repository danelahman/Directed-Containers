{-# OPTIONS --type-in-type #-}

open import Utils 
open import Functors
open import Containers

module Examples.ListContainer  where

open Container
open Functor

-- Lists as a container --

ListCon : Container
ListCon = Nat ◁ Fin

nil' : ∀ {X} → omap ⟦ ListCon ⟧₀ X
nil' = zero , (λ ())

--cons' : ∀ {X} → X → ⟦ ListCon ⟧₀ X → ⟦ ListCon ⟧₀ X
--cons' {X} x (s , f) = (suc s) , f' where
--        f' : Fin (suc s) → X
--        f' zero = x
--        f' (suc s') = f s'

cons' : ∀ {X} → X → omap ⟦ ListCon ⟧₀ X → omap ⟦ ListCon ⟧₀ X
cons' {X} x p = (suc (∃.fst∃(p))) , f' where
        f' : Fin (suc (∃.fst∃(p))) → X
        f' zero = x
        f' (suc s') = ∃.snd∃(p) s'

conv : ∀ {X} → List X → omap ⟦ ListCon ⟧₀ X
conv nil = nil'
conv (cons x xs) = cons' x (conv xs)

conv' : ∀{X} → omap ⟦ ListCon ⟧₀ X → List X
conv' (zero , f) = nil
conv' (suc s , f) =  cons (f zero) (conv' (s , (λ p → f (suc p))))

lem0 : ∀{X} → (x : X) → (xs : omap ⟦ ListCon ⟧₀ X) → (ys : omap ⟦ ListCon ⟧₀ X) → xs == ys → (cons' x xs) == (cons' x ys)
lem0 x p .p refl = refl

lem1 : ∀{X} → (x : X) → (xs : List X) → (ys : omap ⟦ ListCon ⟧₀ X) → xs == (conv' ys) → (cons x xs) == (conv' (cons' x ys))
lem1 x nil (zero , f) p = refl
lem1 x nil (suc s , f) ()
lem1 x (cons x' xs) (zero , f) ()
lem1 x (cons .(f zero) .(conv' (s , λ p' → f (suc p')))) (suc s , f) refl = refl

lem2 : ∀{X} → (xs : List X) → xs == conv' (conv xs)
lem2 nil = refl
lem2 (cons x xs) with conv (cons x xs)
lem2 (cons x xs) | s , f = cong (cons x) (trans (lem2 xs) (cong conv' refl))

StreamCon : Container
StreamCon = ⊤ ◁ λ _ → Nat

stail : StreamCon ⇒ StreamCon
stail = (λ x → x) ◁' (λ _ → suc)


-- Non-empty lists

NEListCon : Container
NEListCon = Nat ◁ (λ n → Fin (suc n))

head : NEListCon ⇒ Id-Con
head = (λ _ → _) ◁' (λ _ _ → zero)

tail : NEListCon ⇒ ListCon
tail = (λ x → x) ◁' (λ _ → suc)