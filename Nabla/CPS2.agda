
-- From:
-- http://gallium.inria.fr/~xleroy/publi/cps-dargaye-leroy.pdf

module CPS2 where

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
open import TermRed

open Term-Structure Tm-Monad

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

lemma5'' : ∀ {a P} {M : Tm a} -> ([0≔ psi M ] P) ≈ ([0≔ ƛ P ] cpsP M ♦)
lemma5'' {a} {P} {var x}  {v'} r2 = β r2
lemma5'' {a} {P} {ƛ M}    {v'} r2 = β (tr (λ t → substT (0≔ ƛ t) P ⟶ v') (! subst-ext^-subst0-wk^-id 1) r2)
lemma5'' {a} {P} {M $$ N} {v'} r2 = β (tr (λ t → t ⟶ v')
    (({!lemma5'' !} ∙ ap (substT _) (! cpsP-wk-naturality M)) ∙ ! subst-hom′ _ _ (cpsP (wk M) ♦)) r2)

lemma5' : ∀ {a P} {M v : Tm a} -> (M ⟶ v) -> ([0≔ psi v ] P) ≈ ([0≔ ƛ P ] cpsP M ♦)
lemma5' {M = M} noop r2 = lemma5'' {M = M} r2
lemma5' {a} {P} (ƛ r1) r2
  {-
    t ⟶ t'
    [0≔ ƛ (ƛ (cpsP t')) ] P ⟶ v'
    -------------------------------------
    [0≔ ƛ (ƛ ([ Φ ] (cpsP t)) ] P ⟶ v'

    where Φ = ext (ext [0≔ ƛ P ]) ∘ renT (map⇑ (map⇑ wkN'))
  -}
  = β ({!lemma5' {!r1!} {!!}!})
  -- (tr (λ t → substT (0≔ t) P ⟶ v') (ap ƛ_ (ap ƛ_ ({!!} ∙ ! lemma4'))) r2)
lemma5' (β r1) r2 = β (β (β {!!}))
lemma5' (r1 $$ r2) r3 = β {!!}

lemma5 : ∀{a} {M v : Tm a} {P : ScopeF Tm a} -> (M ⟶ v) -> ([0≔ psi v ] P) ≈ (cps M $$ ƛ P)
lemma5 r1 r2 = β (lemma5' r1 r2)

theorem : ∀{a} (M : Tm a) -> app (cps M) idTm ⟶ psi M
theorem M = lemma5 {M = M} {v = M} {P = var (new ◆)} noop noop

-- In the terms obtained by the proof, all the names are gone; so
-- there is no help to get from the current instances for inclusions.

-- However, there may be another set of instances which may help.
-- -}
-- -}
-- -}
-- -}
