{-# OPTIONS --type-in-type #-}

open import Utils 
open import Examples.ListDContainer
open import Examples.StreamDContainer
open import Examples.BinaryTreeDContainer1
open import Examples.BinaryTreeDContainer2
open import DContainers

module Examples.Morphisms  where

-- From a list to its head list (without last element)

ListToHeadList : ListDCon ⇒ ListDCon
ListToHeadList = record{sf = sf ; pf = pf ; ax6 = λ {n} {p} → ax6 {n} {p} ; ax7 = ax7; ax8 = λ {n} → ax8 {n}} where
  sf : Nat → Nat
  sf zero = zero
  sf (suc n) = n

  pf : {n : Nat} → Fin (suc (sf n)) → Fin (suc n)
  pf {zero} p = p
  pf {suc n} zero = zero
  pf {suc zero} (suc ())
  pf {suc (suc n)} (suc zero) = suc (pf zero)
  pf {suc (suc n)} (suc (suc p)) = suc (pf (suc p))

  ax6-lem : {n : Nat} → (p : Fin (suc n)) → DContainer._↓_ ListDCon n p == sf (DContainer._↓_ ListDCon (suc n) (pf p))
  ax6-lem {zero} zero = refl
  ax6-lem {zero} (suc ())
  ax6-lem {suc n} zero = refl
  ax6-lem {suc zero} (suc zero) = refl
  ax6-lem {suc zero} (suc (suc ()))
  ax6-lem {suc (suc n)} (suc zero) = refl
  ax6-lem {suc (suc n)} (suc (suc p)) = ax6-lem (suc p)

  ax6 : {n : Nat} → {p : Fin (suc (sf n))} → DContainer._↓_ ListDCon (sf n) p == sf (DContainer._↓_ ListDCon n (pf p))
  ax6 {zero} = refl
  ax6 {suc n} {p} = ax6-lem p

  ax7 : {n : Nat} → _==_ {Fin (suc n)} (pf zero) {Fin (suc n)} zero
  ax7 {zero} = refl
  ax7 {suc n} = refl

  ax8-lem : {n : Nat} → (p  : Fin (suc n)) → (p' : Fin (suc (DContainer._↓_ ListDCon n p))) → pf (suc (DContainer._⊕_ ListDCon p p')) == DContainer._⊕_ ListDCon (pf (suc p)) (pf (subst (λ n' → Fin (suc n')) p' (ax6-lem (suc p))))
  ax8-lem {zero} zero zero = refl
  ax8-lem {zero} zero (suc ())
  ax8-lem {zero} (suc ()) p'
  ax8-lem {suc n} zero zero = refl
  ax8-lem {suc n} zero (suc p') = refl
  ax8-lem {suc n} (suc p) p' = cong suc (ax8-lem p p')

  ax8 : {n : Nat} → (p : Fin (suc (sf n))) (p' : Fin (suc (DContainer._↓_ ListDCon (sf n) p))) → pf {n} (DContainer._⊕_ ListDCon p p') == DContainer._⊕_ ListDCon {n} (pf p) (pf (subst (λ n → Fin (suc n)) p' (ax6 {n})))
  ax8 {zero} p p' = refl
  ax8 {suc zero} zero _ = refl
  ax8 {suc (suc n)} zero _ = refl
  ax8 {suc zero} (suc ()) p'
  ax8 {suc (suc n)} (suc p) p' = ax8-lem p p'


-- From a list to a list with every second element removed

ListToDiv2List : ListDCon ⇒ ListDCon
ListToDiv2List = record{sf = sf ; pf = pf ; ax6 = λ {s} → ax6 {s}; ax7 = ax7; ax8 = λ {s} → ax8 {s}} where
  sf : Nat → Nat
  sf zero = zero
  sf (suc zero) = zero
  sf (suc (suc n)) = suc (sf n)

  pf : {s : Nat} → Fin (suc (sf s)) → Fin (suc s)
  pf {zero} p = p
  pf {suc n} zero = zero
  pf {suc zero} (suc ())
  pf {suc (suc n)} (suc p) = suc (suc (pf p))

  ax6 : {n : Nat} {p : Fin (suc (sf n))} → DContainer._↓_ ListDCon (sf n) p == sf (DContainer._↓_ ListDCon n (pf p))
  ax6 {zero} = refl
  ax6 {suc zero} {zero} = refl
  ax6 {suc (suc n)} {zero} = refl
  ax6 {suc zero} {suc ()}
  ax6 {suc (suc n)} {suc p} = ax6 {n} {p}

  ax7 : {n : Nat} → _==_ {Fin (suc n)} (pf {n} zero) {Fin (suc n)} zero
  ax7 {zero} = refl
  ax7 {suc n} = refl

  ax8 : {n : Nat} (p : Fin (suc (sf n))) (p' : Fin (suc (DContainer._↓_ ListDCon (sf n) p))) → pf (DContainer._⊕_ ListDCon p p') == DContainer._⊕_ ListDCon (pf p) (pf (subst (λ n → Fin (suc n)) p' (ax6 {n})))
  ax8 {zero} p p' = refl
  ax8 {suc zero} zero _ = refl
  ax8 {suc (suc n)} zero _ = refl
  ax8 {suc zero} (suc ()) p'
  ax8 {suc (suc n)} (suc zero) p' = cong suc (cong suc (ax8 zero p'))
  ax8 {suc (suc n)} (suc (suc p)) p' = cong suc (cong suc (ax8 (suc p) p'))


-- From a list to singleton head list (identity directed container) --

ListToHead : ListDCon ⇒ Id-DCon
ListToHead = record{sf = λ _ → tt ; pf = pf ; ax6 = λ {n} {p} → refl ; ax7 = ax7; ax8 = ax8} where
  pf : {n : Nat} → ⊤ → Fin (suc n)
  pf _ = zero

  ax7 : {n : Nat} → _==_ {Fin (suc n)} zero {Fin (suc n)} zero
  ax7 = refl

  ax8 : {n : Nat} → (p p' : ⊤) → _==_ {Fin (suc n)} zero {Fin (suc n)} (DContainer._⊕_ ListDCon {n} zero zero)
  ax8 {zero} p p' = refl
  ax8 {suc n} p p' = refl


-- From a stream to a stream with every second element removed

StreamToDiv2Stream : StreamDCon ⇒ StreamDCon
StreamToDiv2Stream = record{sf = λ s → tt ; pf = λ p → p *nat 2 ; ax6 = λ {s} {p} → refl; ax7 = λ {s} → refl; ax8 = λ {s} → ax8 {s}} where
  ax8-lem : {s : ⊤} → (p : Nat) → (DContainer._⊕_ StreamDCon {s} p 0 *nat 2) == (p *nat 2)
  ax8-lem zero = refl
  ax8-lem (suc p) = cong suc (cong suc (ax8-lem p))

  ax8-lem2 : {s : ⊤} → (p : Nat) → (p *nat 2) == DContainer._⊕_ StreamDCon {s} (p *nat 2) 0
  ax8-lem2 zero = refl
  ax8-lem2 (suc p) = cong suc (cong suc (ax8-lem2 p))

  ax8-lem3 : {s : ⊤} → (p p' : Nat) → (DContainer._⊕_ StreamDCon {s} p (suc p') *nat 2) == DContainer._⊕_ StreamDCon {s} (p *nat 2) (suc (suc (p' *nat 2)))
  ax8-lem3 zero p' = refl
  ax8-lem3 (suc p) p' = cong suc (cong suc (ax8-lem3 p p'))

  ax8 : {s : ⊤} → (p p' : Nat) → (DContainer._⊕_ StreamDCon p p' *nat 2) == DContainer._⊕_ StreamDCon (p *nat 2) (p' *nat 2)
  ax8 zero p' = refl
  ax8 (suc p) zero = cong suc (cong suc (trans (ax8-lem p) (ax8-lem2 p)))
  ax8 (suc p) (suc p') = cong suc (cong suc (ax8 p (suc p')))



-- From an infinite binary tree to its mirror tree --

InfBTreeToMirrorInfBTree : InfBTreeDCon ⇒ InfBTreeDCon
InfBTreeToMirrorInfBTree = record{sf = λ _ → tt ; pf = λ {s} → pf {s}; ax6 = λ {s} {p} → refl; ax7 = λ {s} → refl; ax8 = λ {s} → ax8 {s}} where
  pf : {s : ⊤} → List Choice → List Choice
  pf nil = nil
  pf (cons lc ps) = cons rc (pf {tt} ps)
  pf (cons rc ps) = cons lc (pf {tt} ps)

  ax8 : {s : ⊤} → (p p' : List Choice) → pf (DContainer._⊕_ InfBTreeDCon p p') == DContainer._⊕_ InfBTreeDCon (pf p) (pf p')
  ax8 nil p' = refl
  ax8 {void} (cons lc ps) p' = cong (cons rc) (ax8 {void} ps p')
  ax8 {void} (cons rc ps) p' = cong (cons lc) (ax8 {void} ps p')



-- From a finite binary tree to its mirror tree --

FinBTreeToMirrorFinBTree : FinBTreeDCon ⇒ FinBTreeDCon
FinBTreeToMirrorFinBTree = record{sf = sf ; pf = pf; ax6 = λ {s} {p} → ax6 {s} {p}; ax7 = λ {s} → ax7 {s}; ax8 = λ {s} → ax8 {s}} where
  sf : TreeShape → TreeShape
  sf (nd nothing nothing) = (nd nothing nothing)
  sf (nd (just l) nothing) = (nd nothing (just (sf l)))
  sf (nd nothing (just r)) = (nd (just (sf r) ) nothing)
  sf (nd (just l) (just r)) = (nd (just (sf r) ) (just (sf l) ))

  pf : {s : TreeShape} → TreePos (sf s) → TreePos s
  pf {nd nothing nothing} p = p
  pf {nd (just l) nothing} stop = stop
  pf {nd (just l) nothing} (right p) = left (pf p)
  pf {nd nothing (just r)} stop = stop
  pf {nd nothing (just r)} (left p) = right (pf p)
  pf {nd (just l) (just r)} stop = stop
  pf {nd (just l) (just r)} (left p) = right (pf p)
  pf {nd (just l) (just r)} (right p) = left (pf p)

  ax6 : {s : TreeShape} → {p : TreePos (sf s)} → DContainer._↓_ FinBTreeDCon (sf s) p == sf (DContainer._↓_ FinBTreeDCon s (pf p))
  ax6 {nd nothing nothing} {stop} = refl
  ax6 {nd (just l) nothing} {stop} = refl
  ax6 {nd (just l) nothing} {right p} = ax6 {l} {p}
  ax6 {nd nothing (just r)} {stop} = refl
  ax6 {nd nothing (just r)} {left p} = ax6 {r} {p}
  ax6 {nd (just l) (just r)} {stop} = refl
  ax6 {nd (just l) (just r)} {left p} = ax6 {r} {p}
  ax6 {nd (just l) (just r)} {right p} = ax6 {l} {p}

  ax7 : {s : TreeShape} → pf (DContainer.o FinBTreeDCon) == DContainer.o FinBTreeDCon
  ax7 {nd nothing nothing} = refl
  ax7 {nd (just l) nothing} = refl
  ax7 {nd nothing (just r)} = refl
  ax7 {nd (just l) (just r)} = refl

  ax8 : {s : TreeShape} → (p : TreePos (sf s)) → (p' : TreePos (DContainer._↓_ FinBTreeDCon (sf s) p)) → pf (DContainer._⊕_ FinBTreeDCon p p') == DContainer._⊕_ FinBTreeDCon (pf p) (pf (subst TreePos p' (ax6 {s})))
  ax8 {nd nothing nothing} stop p' = refl
  ax8 {nd (just l) nothing} stop p' = refl
  ax8 {nd (just l) nothing} (right p) p' = cong left (ax8 p p')
  ax8 {nd nothing (just r)} stop p' = refl
  ax8 {nd nothing (just r)} (left p) p' = cong right (ax8 p p')
  ax8 {nd (just l) (just r)} stop p' = refl
  ax8 {nd (just l) (just r)} (left p) p' = cong right (ax8 p p')
  ax8 {nd (just l) (just r)} (right p) p' = cong left (ax8 p p')
