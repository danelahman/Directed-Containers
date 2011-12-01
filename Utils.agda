{-# OPTIONS --type-in-type #-}

module Utils where

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ⊥ → ∀ T → T
⊥-elim () T

data _==_ {A : Set}(a : A) : {A' : Set} → A' → Set where
  refl : a == a

sym : {A A' : Set} → {a : A}{a' : A'} → a == a' → a' == a
sym refl = refl

data _=='_ {A : Set}(a : A) : A → Set where
  refl : a ==' a

postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ a → f a == g a) → f == g

postulate ext' : {A A' : Set}{B : A → Set}{B' : A' → Set}{f : ∀ a → B a}{g : ∀ a → B' a} → 
                (∀ {a} {a'} → a == a' → f a == g a') → f == g


postulate iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ a → f {a} == g {a}) → 
                 _==_ { {a : A} → B a} f { {a : A} → B' a} g

postulate iext' : {A A' : Set}{B : A → Set}{B' : A' → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ {a} {a'} → a == a' → f {a} == g {a'}) → 
                 _==_ { {a : A} → B a} f { {a : A'} → B' a} g

postulate iext2 : {A : Set}{B : A → Set}{C C' : ∀ a → B a → Set} {f : ∀ {a} {b} → C a b}{g : ∀{a} {b} → C' a b} → 
                 (∀ a b → f {a} {b} == g {a} {b}) → 
                 _==_ {∀ {a} {b} → C a b} f {∀{a} {b} → C' a b} g

postulate iext3 : {A A' : Set}{B : A → Set}{B' : A' → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} → 
                 (∀ {a} {b} → a == b → f {a} == g {b}) → 
                 _==_ { {a : A} → B a} f { {a : A'} → B' a} g

cong : {A B : Set} → (f : A → B) → {a a' : A} → a == a' → f a == f a'
cong f refl = refl

dcong : {A : Set}{B : A → Set} → (f : (a : A) → B a) → {a a' : A} → a == a' → f a == f a'
dcong f refl = refl

trans : {A B C : Set} → {a : A} → {b : B} → {c : C} → a == b → b == c → a == c
trans refl refl = refl

subst : {A : Set} → (C : A → Set) → {a : A} → C a → {b : A} → a == b → C b
subst C p refl = p

substtrans : {A : Set} → (C : A → Set) → {a : A} → (t : C a) → {b : A} → (p : a == b) → {c : A} → (q : b == c) → subst C (subst C t p) q == subst C t (trans p q)
substtrans C t refl refl = refl

substcong : {A B : Set} → (P : B → Set) → (f : A → B) → {a a' : A} → (t : P (f a)) → (p : a == a') → subst (λ t → P (f t)) t p == subst P t (cong f p)
substcong P f t refl = refl

substcong2 : {A B : Set} → (P : A → Set) → (Q : B → Set) → (f : A → B) → (pf : ∀ {a} → Q (f a) → P a) → {a a' : A} → (t : Q (f a)) → (p : a == a') → subst P (pf t) p == pf (subst Q t (cong f p))
substcong2 P Q f pf t refl = refl

stripsubst : {A : Set} → (C : A → Set) → {a : A} → (c : C a) → {b : A} → (p : a == b) → subst C c p == c
stripsubst C c refl = refl 

ir : ∀ {A A' : Set}{a : A}{a' : A'}{p q : a == a'} → p == q
ir {p = refl}{q = refl} = refl

fixtypes : ∀{A A' : Set}{a a' : A}{a'' a''' : A'}{p : a == a'}{q : a'' == a'''} → a == a'' → a' == a''' → p == q
fixtypes refl refl = ir        

fixtypesX : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''}{p : a == a'}{q : a'' == a'''} → a == a'' → a' == a''' → p == q
fixtypesX refl refl = ir

cong2' : {A : Set}{B : Set}{C : ∀ a b → Set} → (f : ∀ a b → C a b) → {a a' : A} → a == a' → {b b' : B} → b == b' → f a b == f a' b'
cong2' f refl refl = refl

cong2 : {A : Set}{B : A → Set}{C : ∀ a → B a → Set} → (f : ∀ a b → C a b) → {a a' : A} → a == a' → {b : B a} → {b' : B a'} → b == b' → f a b == f a' b'
cong2 f refl refl = refl

cong2'' : {A : Set}{B : A → Set}{B' : A → Set} → B == B' → {C : ∀ a → B a → Set}{C' : ∀ a → B' a → Set} → C == C' → {f : ∀ a b → C a b} → {f' : ∀ a b → C' a b} → f == f' → {a a' : A} → a == a' → {b : B a} → {b' : B' a'} → b == b' → f a b == f' a' b'
cong2'' refl refl refl refl refl = refl

cong2''' : {A A' : Set} → A == A' → {B : A → Set}{B' : A' → Set} → B == B' → {C : ∀ a → B a → Set}{C' : ∀ a → B' a → Set} → C == C' → {f : ∀ a b → C a b} → {f' : ∀ a b → C' a b} → f == f' → {a : A} → {a' : A'} → a == a' → {b : B a} → {b' : B' a'} → b == b' → f a b == f' a' b'
cong2''' refl refl refl refl refl refl = refl

cong3 : {A : Set}{B : A → Set}{C : ∀ a → B a → Set}{D : ∀ a b → C a b → Set} → (f : ∀ a b c → D a b c) → {a a' : A} → a == a' → {b : B a} → {b' : B a'} → b == b' → {c : C a b} → {c' : C a' b'} → c == c' → f a b c == f a' b' c'
cong3 f refl refl refl = refl

cong3' : {A A' : Set} → A == A' → {B : A → Set}{B' : A' → Set} → B == B' → {C : ∀ a → B a → Set}{C' : ∀ a → B' a → Set} → C == C' → {D : ∀ a → (b : B a) → C a b → Set}{D' : ∀ a → (b : B' a) → C' a b → Set} → D == D' → {f : ∀ a b c → D a b c} → {f' : ∀ a b c → D' a b c} → f == f' → {a : A} → {a' : A'} → a == a' → {b : B a} → {b' : B' a'} → b == b' → {c : C a b} → {c' : C' a' b'} → c == c' → f a b c == f' a' b' c'
cong3' refl refl refl refl refl refl refl refl = refl


cong3'' : {A : Set}{B : A → Set}{B' : A → Set} → B == B' → {C : ∀ a → B a → Set}{C' : ∀ a → B' a → Set} → C == C' → {D : ∀ a → (b : B a) → C a b → Set}{D' : ∀ a → (b : B' a) → C' a b → Set} → D == D' → {f : ∀ a b c → D a b c} → {f' : ∀ a b c → D' a b c} → f == f' → {a a' : A} → a == a' → {b : B a} → {b' : B' a'} → b == b' → {c : C a b} → {c' : C' a' b'} → c == c' → f a b c == f' a' b' c'
cong3'' refl refl refl refl refl refl refl = refl

cong4 : {A : Set}{B : A → Set}{C : ∀ a → B a → Set}{D : ∀ a b → C a b → Set}{E : ∀ a b c → D a b c → Set} → (f : ∀ a b c d → E a b c d) → {a a' : A} → a == a' → {b : B a} → {b' : B a'} → b == b' → {c : C a b} → {c' : C a' b'} → c == c' → {d : D a b c} → {d' : D a' b' c'} → d == d' → f a b c d == f a' b' c' d'
cong4 f refl refl refl refl = refl

cong5 : {A F : Set}{B : A → Set}{C D : ∀ a → B a → Set}{E : ∀ a (b : B a) (c : C a b) → Set}→ (f : ∀ a b c → D a b → E a b c → F) → {a a' : A} → a == a' → {b : B a} → {b' : B a'} → b == b' → {c : C a b} → {c' : C a' b'} → c == c' → {d : D a b} → {d' : D a' b'} → d == d'  → {e : E a b c} → {e' : E a' b' c'} → e == e' → f a b c d e == f a' b' c' d' e'
cong5 f refl refl refl refl refl = refl

cong6 : {A : Set}{B : A → Set}{C : ∀ a → B a → Set}{D : ∀ a b → C a b → Set}{E : ∀ a b c → D a b c → Set}{F : ∀ a b c d → E a b c d → Set}{G : ∀ a b c d e → F a b c d e → Set} → (g : ∀ a b c d e f → G a b c d e f) → {a a' : A} → a == a' → {b : B a} → {b' : B a'} → b == b' → {c : C a b} → {c' : C a' b'} → c == c' → {d : D a b c} → {d' : D a' b' c'} → d == d' → {e : E a b c d} → {e' : E a' b' c' d'} → e == e' → {f : F a b c d e} → {f' : F a' b' c' d' e'} → f == f' → g a b c d e f == g a' b' c' d' e' f'
cong6 f refl refl refl refl refl refl = refl

cong10 : {A : Set}{B : A → Set}{C : ∀ a → B a → Set}{D : ∀ a b → C a b → Set}{E : ∀ a b c → D a b c → Set}{F : ∀ a b c d → E a b c d → Set}{G : ∀ a b c d e → F a b c d e → Set}{H : ∀ a b c d e f → G a b c d e f → Set}{I : ∀ a b c d e f g → H a b c d e f g → Set}{J : ∀ a b c d e f g h → I a b c d e f g h → Set}{K : ∀ a b c d e f g h i → J a b c d e f g h i → Set} → (k : ∀ a b c d e f g h i j → K a b c d e f g h i j) → {a a' : A} → a == a' → {b : B a} → {b' : B a'} → b == b' → {c : C a b} → {c' : C a' b'} → c == c' → {d : D a b c} → {d' : D a' b' c'} → d == d' → {e : E a b c d} → {e' : E a' b' c' d'} → e == e' → {f : F a b c d e} → {f' : F a' b' c' d' e'} → f == f' → {g : G a b c d e f} → {g' : G a' b' c' d' e' f'} → g == g' → {h : H a b c d e f g} → {h' : H a' b' c' d' e' f' g'} → h == h' → {i : I a b c d e f g h} → {i' : I a' b' c' d' e' f' g' h'} → i == i' →  {j : J a b c d e f g h i} → {j' : J a' b' c' d' e' f' g' h' i'} → j == j' → k a b c d e f g h i j == k a' b' c' d' e' f' g' h' i' j'
cong10 f refl refl refl refl refl refl refl refl refl refl = refl

cong' : {A A' : Set}{a : A}{a' : A'} → a == a' → {B : A → Set}{B' : A' → Set} → B == B' → {f : ∀ a → B a} → {f' : ∀ a → B' a} → f == f' → f a == f' a'
cong' refl refl refl = refl

icong : {A : Set}{B : A → Set} → (f : {a : A} → B a) → {a a' : A} → a == a' → f {a} == f {a'}
icong f refl = refl

icong' : {A A' : Set}{a : A}{a' : A'} → a == a' → {B : A → Set}{B' : A' → Set} → B == B' → {f : ∀ {a} → B a} → {f' : ∀ {a} → B' a} → _==_ {∀ {a} → B a} f {∀ {a} → B' a} f' → f {a} == f' {a'}
icong' refl refl refl = refl

iecong : {A A' : Set}{B : A → Set}{B' : A' → Set}{C : ∀ a → B a → Set}{C' : ∀ a → B' a → Set} → {a : A} → {a' : A'} → a == a' → B == B' → {b : B a} → {b' : B' a'} → b == b' →  C == C' → {f : ∀ {a} b → C a b} → {f' : ∀ {a} b → C' a b} → _==_ {∀ {a} b → C a b} f {∀ {a} b → C' a b} f' → f {a} b == f' {a'} b'
iecong refl refl refl refl refl = refl

iecong' : {A A' : Set}{B : A → Set}{B' : A' → Set}{C : ∀ a → B a → Set}{C' : ∀ a → B' a → Set}{D : ∀ a → (b : B a) → C a b → Set}{D' : ∀ a → (b : B' a) → C' a b → Set} → {a : A} → {a' : A'} → a == a' → B == B' → {b : B a} → {b' : B' a'} → b == b' →  C == C' → {c : C a b} → {c' : C' a' b'} → c == c' → D == D' → {f : ∀ {a} b c → D a b c} → {f' : ∀ {a} b c → D' a b c} → _==_ {∀ {a} b c → D a b c} f {∀ {a} b c → D' a b c} f' → f {a} b c == f' {a'} b' c'
iecong' refl refl refl refl refl refl refl = refl

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

+elim : {A B : Set} -> {C : A + B -> Set} -> ((a : A) -> C (inl a)) -> ((b : B) -> C (inr b)) -> (c : A + B) -> C c
+elim d e (inl a) = d a
+elim d e (inr b) = e b

+elim-lem-l : {A : Set} {p p' : A} {C : (p == p') + ((p == p') → ⊥) -> Set} → (f : ∀ a -> C (inl a)) -> (g : ∀ b -> C (inr b)) → (c : (p == p') + ((p == p') → ⊥)) → (q : p == p') → (+elim {C = C} f g c) == f q
+elim-lem-l f g (inl refl) refl = refl
+elim-lem-l f g (inr p) q = ⊥-elim (p q) _

+elim-lem-r : {A : Set} {p p' : A} {C : (p == p') + ((p == p') → ⊥) -> Set} → (f : ∀ a -> C (inl a)) -> (g : ∀ b -> C (inr b)) → (c : (p == p') + ((p == p') → ⊥)) → (q : p == p' → ⊥) → (+elim {C = C} f g c) == g q
+elim-lem-r f g (inl p) q = ⊥-elim (q p) _
+elim-lem-r f g (inr p) q = dcong g (ext (λ a → ⊥-elim (p a) _))



infixl 10 _+_

data Bool : Set where
  true false : Bool

_or_ : Bool -> Bool -> Bool 
true or _ = true
false or x = x

_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else _ = x
if false then _ else y = y


record ∃ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field fst∃ : A
        snd∃ : B fst∃

eq-lem : {A A' : Set} → {a : A} → {a' : A'} → a == a' → A == A'
eq-lem refl = refl

∃-eq : {A A' : Set} → {B : A → Set} → {B' : A' → Set} → B == B' → {p : ∃ A B} → {p' : ∃ A' B'} → ∃.fst∃ p == ∃.fst∃ p' → ∃.snd∃ p == ∃.snd∃ p' → p == p'
∃-eq p' p q with eq-lem p
∃-eq refl p q | refl = cong2 _,_ p q

∃-eqfst : {A A' : Set} → A == A' → {B : A → Set} → {B' : A' → Set} → B == B' → {p : ∃ A B} → {p' : ∃ A' B'} → p == p' → ∃.fst∃ p == ∃.fst∃ p'
∃-eqfst refl refl refl = refl

∃-eqsnd : {A A' : Set} → A == A' → {B : A → Set} → {B' : A' → Set} → B == B' → {p : ∃ A B} → {p' : ∃ A' B'} → p == p' → ∃.snd∃ p == ∃.snd∃ p'
∃-eqsnd refl refl refl = refl

_×_ : Set → Set → Set
A × B = ∃ A λ _ → B

infixl 10 _×_
infixl 10 _,_

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

_+nat_ : Nat → Nat → Nat
zero  +nat n = n
suc m +nat n = suc (m +nat n)

{-# BUILTIN NATPLUS _+nat_ #-}

_-nat_ : Nat → Nat → Nat
m     -nat zero  = m
zero  -nat suc n = zero
suc m -nat suc n = m -nat n

{-# BUILTIN NATMINUS _-nat_ #-}

_*nat_ : Nat → Nat → Nat
zero  *nat n = zero
suc m *nat n = n +nat m *nat n

{-# BUILTIN NATTIMES _*nat_ #-}

div2 : Nat → Nat
div2 zero          = zero
div2 (suc zero)    = zero
div2 (suc (suc n)) = suc (div2 n)

div2' : Nat → Nat
div2' n = div2 (suc n)

infixl 6 _+nat_

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A 

data List' (A : Set) : Set where
  nil : List' A
  snoc : List' A → A → List' A

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc : {n : Nat} → Fin n → Fin (suc n)

nat2fin : (n : Nat) → Fin (suc n)
nat2fin zero = zero
nat2fin (suc n) = suc (nat2fin n)

fin2nat : {n : Nat} → Fin n → Nat
fin2nat zero = zero
fin2nat (suc n) = suc (fin2nat n)

data Fin' : Nat → Set where
  zero : {n : Nat} → Fin' n
  suc : {n : Nat} → Fin' n → Fin' (suc n)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

maybe-elim : ∀{A B} → Maybe A → (A → B) → B → B
maybe-elim nothing  j n = n
maybe-elim (just a) j n = j a

just-elim : {A A' : Set} → A == A' → {a : A} → {a' : A'} → just a == just a' → a == a'
just-elim refl refl = refl

identity : {A : Set} -> A -> A 
identity {A} x = x

_·_ : {A B C : Set} → (f : A → B) → (g : C → A) → C → B
(f · g) x = f (g x)

·assoc : {A B C D : Set} → {f : A → B} → {g : B → C} → {h : C → D} → h · g · f == h · (g · f)
·assoc = refl

·lunit : {A B : Set} → {f : A → B} → identity · f == f
·lunit = refl

·runit : {A B : Set} → {f : A → B} → f · identity == f
·runit = refl

infixl 60 _·_

record Monoid : Set where
  constructor monoid
  field M : Set
        e : M
        _*_ : M → M → M

        monoid-assoc : (a b c : M) → (a * b) * c == a * (b * c)
        monoid-id1 : (a : M) → a * e == a
        monoid-id2 : (a : M) → e * a == a

  infixl 50 _*_


record Iso (X Y : Set) : Set where
  constructor _≅_
  field i : X → Y
        j : Y → X
        iso-ax1 : i · j == identity {Y}
        iso-ax2 : j · i == identity {X}
