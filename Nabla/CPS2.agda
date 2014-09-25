
-- From:
-- http://gallium.inria.fr/~xleroy/publi/cps-dargaye-leroy.pdf

module CPS2 where

open import Data.List
open import Data.Product hiding (map)
open import Data.Maybe hiding (module Eq; Eq; map)
open import Data.Nat
open import Function

open import Sketch5
open import Terms

load : ∀ {w b}  -> w -> w ▹ b -> w
load _ (old x) = x
load v (new _) = v

{-# NO_TERMINATION_CHECK #-}
mutual 
  psi : ∀ {a} -> Tm a -> Tm a
  psi (lam M) = lam (pack Tm λ κ0 -> atVar Tm (cps M) κ0)
  psi x = x

  cps : ∀ {a} -> Tm a -> Tm a
  cps (app M N) = lam (pack Tm λ κ0 -> app (cps (wk M)) (lam (pack Tm λ k1 →
                                       app (cps (wk N)) (lam (pack Tm λ k2 ->
                                       app (app (var' k2) (var' k1)) (var' κ0))))))
  cps A = lam (pack Tm (λ κ0 → app (var' κ0) (wk $ psi A))) -- Or psi (wk A)

data _⟶_ {α} : (t u : Tm α) → Type where
  val : ∀{v} -> v ⟶ v
  β     : ∀ {t u v} → [0≔ u ] t ⟶ v -> app (lam t) u ⟶ v
  _·_ : ∀ {t t' u u'}(r : t ⟶ t') (q : u ⟶ u') -> app t u ⟶ app t'  u'
  ƛ_  : ∀ {t t'}(r : t ⟶ t') → lam t ⟶ lam t'


-- lem : ∀{PsubstT (subst0 (lam (substT (ext (subst0 (lam .P))) (substT (ext (λ x → var (old x))) (cps M))))) .P == ?
-- lem = ?

lemma5 : ∀{a} {M v v' : Tm a} {P : ScopeF Tm a} -> (M ⟶ v) -> (substituteOut _ (psi v) P) ⟶ v' -> app (cps M) (lam P) ⟶ v'
lemma5 {M = var x} val r2 = β (β r2)
lemma5 {M = lam M} val r2 = β (β {!!}) --1
lemma5 {M = app M M₁} val r2 = β {!lemma5!} --2
lemma5 (β r1) r2 = β (β (β {!!})) 
lemma5 (r1 · r2) r3 = β {!!} --2
lemma5 (ƛ r1) r2 = β (β {!!}) --1

identity : ∀ {α} -> Tm α
identity = lam (var (new _))

theorem : ∀{a} (M : Tm a) -> app (cps M) identity ⟶ psi M
theorem M = lemma5 {M = M} {v = M} {P = var (new ◆)} val val

 
{-
{-# NO_TERMINATION_CHECK #-}
cps : ∀ {a} -> Tm a -> ScopeF Tm a -> Tm a
cps (var x) k = load x <$> k
cps (lam t) k = [0≔  
                (lam (pack Tm λ x →
                 lam (pack Tm λ k' →
                 cps (wk (atVar' Tm t x))  (var' k')))) ] k
cps (app e1 e2) k = cps e1 (pack Tm λ m →
                    cps (wk e2) (pack Tm λ n →
                    app (app (var' m) (var' n)) (lam (pack Tm (λ x' → atVar' Tm k x')))))



-- Maybe something like that?
theorem : ∀{α} (x y : Tm α) -> x ~> y -> cps x identity ~> y
theorem ._ ._ β = {!!}
theorem ._ ._ ([ p ]· u) = {!!}
theorem ._ ._ (u ·[ p ]) = {!!}
theorem ._ ._ ƛ[ p ] = {!!}

-- In the terms obtained by the proof, all the names are gone; so
-- there is no help to get from the current instances for inclusions.

-- However, there may be another set of instances which may help.
-}
