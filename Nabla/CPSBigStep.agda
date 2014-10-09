module CPSBigStep where

open import Data.Product hiding (map)
open import Data.Maybe hiding (module Eq; Eq; map)
open import Data.Nat
open import Function
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)

open import Sketch5
open import Terms
open import TermRed2

open Term-Structure Tm-Monad hiding (_≔_; ext▹)
open PointedRenaming using (_≔_ ; ext▹)

load : ∀ {w b}  -> w -> w ▹ b -> w
load _ (old x) = x
load v (new _) = v



{-# NO_TERMINATION_CHECK #-}
mutual 
  psi : ∀ {a} -> Tm a -> Tm a
  psi (ƛ M) = lamP λ κ0 -> atVar Tm (cps M) κ0
  psi x = x

  cpsP : ∀ {a} -> Tm a -> ScopeP Tm a
  cpsP (M $$ N) κ0 = cps (wk M) $$
                         (lamP λ k1 →
                           cps (wk N) $$
                               (lamP λ k2 ->
                                  (var' k2 $$ var' k1) $$ var' κ0))
  cpsP A κ0 = var' κ0 $$ (wk $ psi A) -- Or psi (wk A)

  cps : ∀ {a} -> Tm a -> Tm a
  cps A = lamP (cpsP A)

-- supposed to come for free
cpsP-naturality : ∀ {α β} (f : α → β) (t : Tm α) → cpsP (renT f t) ♦ == renT (map⇑ f) (cpsP t ♦)
cpsP-naturality f (var x) = refl
cpsP-naturality f (ƛ x) = ap (λ x₁ → var (new _) $$ ƛ (lam x₁)) {!!}
cpsP-naturality f (t $$ t₁) = {!!}

-- cpsP-naturality : ∀ {α β b b'} (f : α → β) (t : Tm α) → cpsP (renT f t) b == renT (map▹ _ _ f) (cpsP t b')

-- supposed to come for free
cps-naturality : ∀ {α β} (f : α → β) (t : Tm α) → cps (renT f t) == renT f (cps t)
cps-naturality f t = ap lam (cpsP-naturality f t)

cpsP-wk-naturality : ∀ {α} (t : Tm α)
 → cpsP (wk {{box (old {b = ♦}) }} t) ♦ == wk {{box (map⇑ old)}} (cpsP t ♦)
cpsP-wk-naturality = cpsP-naturality old

open ≈-Reasoning

cps-Value : ∀ {α} (M : Tm α) → Value (cps M)
cps-Value M = ƛ (cpsP M ♦)

⟶-cps : ∀ {α} (M : Tm α) → cps M ⟶ cps M
⟶-cps M = ƛ (cpsP M ♦)

lemma5' : ∀ {a P} {M v : Tm a} → (M ⟶ v) → ([ 0≔ psi v ] P) ≈ ([ 0≔ ƛ P ] cpsP M ♦)
lemma5' {P = P} {v = v} (β {t} {t'} {u} {vu} ru rt rt') {v'} rP = β (ƛ _) (ƛ _) (tr (λ x → x ⟶ v') {!bind-assoc' {s = 0≔ (psi v)} {s' = ?} P!} rP)
lemma5' (ƛ t) rP = β (ƛ _) (ƛ _) {!!}

lemma5 : ∀{a} {M v : Tm a} {P : ScopeF Tm a} → (M ⟶ v) → ([ 0≔ psi v ] P) ≈ (cps M $$ ƛ P)
lemma5 {M = M} r r' = β (⟶-cps M) (ƛ _) (lemma5' r r')

⟶-psi : ∀ {α} {v : Tm α} → Value v → psi v ⟶ psi v
⟶-psi (ƛ t) = ƛ _

theorem : ∀{a} (M v : Tm a) → M ⟶ v → cps M $$ idTm ⟶ psi v
theorem M v r = lemma5 {M = M} {v = v} {P = var (new ◆)} r (⟶-psi (⟶-Value r))