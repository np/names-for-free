
-- From:
-- http://gallium.inria.fr/~xleroy/publi/cps-dargaye-leroy.pdf

module CPS2 where

open import Data.List
open import Data.Product hiding (map)
open import Data.Maybe hiding (module Eq; Eq; map)
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)

open import Sketch5
open import Terms

load : ∀ {w b}  -> w -> w ▹ b -> w
load _ (old x) = x
load v (new _) = v

wkTm : ∀ {α β} {{s : α ⇉ β}} → Tm α → Tm β
wkTm = wk {{Tm-Functor}}

ext-var' : ∀ {α β}(s : α → β) → ext (var ∘ s) ~ var ∘ map⇑ s
ext-var' s (old x) = refl
ext-var' s (new .♦) = refl

-- ext-map⇑ : ∀ {α b}(t : Tm α) → ext (subst0 {b = b} t) ∘ map⇑ old ~ var
-- ext-map⇑ s (old x) = refl
-- ext-map⇑ s (new .♦) = refl

lemma4 : ∀ {a} {t : Tm (a ⇑)}{u}
  → substT (ext (subst0 {b = ♦} u)) (renT (map⇑ old) t) == t
lemma4 {t = t} {u} = trans (bind∘fmap t _ _) (right-id (ext-map⇑ u) t)

lemma4' : ∀ {a} {t : Tm (a ⇑ ⇑)}{u}
  → substT (ext (ext (subst0 {b = ♦} u))) (renT (map⇑ (map⇑ old)) t) == t
lemma4' {t = t} {u} = trans (bind∘fmap t (map⇑ (map⇑ old)) (ext (ext (subst0 {b = ♦} u)))) {!!}  


{-# NO_TERMINATION_CHECK #-}
mutual 
  psi : ∀ {a} -> Tm a -> Tm a
  psi (ƛ M) = lamP λ κ0 -> atVar Tm (cps M) κ0
  psi x = x

  cpsP : ∀ {a} -> Tm a -> ScopeP Tm a
  cpsP (M $$ N) κ0 = cps (wkTm M) $$
                         (lamP λ k1 →
                           cps (wkTm N) $$
                               (lamP λ k2 ->
                                  (var' k2 $$ var' k1) $$ var' κ0))
  cpsP A κ0 = var' κ0 $$ (wkTm $ psi A) -- Or psi (wk A)

  cps : ∀ {a} -> Tm a -> Tm a
  cps A = lamP (cpsP A)

-- supposed to come for free
cpsP-naturality : ∀ {α β b b'} (f : α → β) (t : Tm α) → cpsP (renT f t) b == renT (map▹ _ _ f) (cpsP t b')
cpsP-naturality = {!!}

-- supposed to come for free
cps-naturality : ∀ {α β} (f : α → β) (t : Tm α) → cps (renT f t) == renT f (cps t)
cps-naturality f t = ap lam (cpsP-naturality f t)

cpsP-wk-naturality : ∀ {α} (t : Tm α)
 → cpsP (wkTm {{mk⇉ (old {b = ♦}) }} t) ♦ == wkTm {{mk⇉ (map⇑ old)}} (cpsP t ♦)
cpsP-wk-naturality = cpsP-naturality old

-- Not used yet
mutual
    -- Neutral forms
    data Neu {α} : Tm α → Type where
      var  : ∀ x → Neu (var x)
      _$$_ : ∀ {t u} → Neu t → Nrm u → Neu (t $$ u)

    -- Normal forms
    data Nrm {α} : Tm α → Type where
      ƛ_  : {t : Tm (α ⇑)} → Nrm t → Nrm (ƛ t)
      neu : ∀ {t} → Neu t → Nrm t

infix 2 _⟶_
data _⟶_ {α} : (t u : Tm α) → Type where
  -- nrm : ∀{v} → Nrm v → v ⟶ v
  noop  : ∀{v} → v ⟶ v
  β    : ∀ {t u v} → [0≔ u ] t ⟶ v -> ƛ t $$ u ⟶ v
  _$$_ : ∀ {t t' u u'}(r : t ⟶ t') (q : u ⟶ u') -> t $$ u ⟶ t' $$ u'
  ƛ_   : ∀ {t t'}(r : t ⟶ t') → ƛ t ⟶ ƛ t'

⟶trans : ∀ {a} {t u v : Tm a} -> (t ⟶ u) -> (u ⟶ v) -> (t ⟶ v)
⟶trans = {!!}

==⟶ : ∀ {a} -> {t u : Tm a} -> (t == u) -> (t ⟶ u)
==⟶ = {!!}

subst-lemma' : ∀ {a b} -> {M M' : Tm a} -> ∀ {s s' : a → Tm b} → (M ⟶ M') -> (∀ x -> s x ⟶ s' x) -> M >>= s ⟶ M' >>= s'
subst-lemma' noop = {!extensionality x!}  
subst-lemma' {a} {b} {._} {M'} {s} {s'} (β {t} {u} r1) x = β (⟶trans (==⟶ (trans (bind-assoc {{Tm-Monad}} {s =(subst0 (substT s u)) } {s' = ext s} {s'' = substT (subst0 (substT s u)) ∘ (ext  s )} (λ x₁ → refl) t) (trans {!ap2 substT ? refl !} (! bind-assoc {{Tm-Monad}} {s = s} {s' = subst0 u} {s'' = substT s ∘ subst0 u} (λ x₁ → refl) t)))) (subst-lemma' {M = substT (subst0 u) t} {M' = M'} {s = s} {s' = s'} r1 x))
subst-lemma' (r1 $$ r2) x = subst-lemma' r1 x $$ subst-lemma' r2 x 
subst-lemma' (ƛ r1) x = ƛ subst-lemma' r1 {!extensionality x!}

subst-lemma : ∀ {a} -> {M v : Tm a} -> (N v' : ScopeF Tm a) → (M ⟶ v) -> (N ⟶ v') -> [0≔ M ] N ⟶ [0≔ v ] v'
subst-lemma = {!!}

lemma5' : ∀ {a P v'} {M v : Tm a} -> (M ⟶ v) -> (substituteOut _ (psi v) P) ⟶ v' -> [0≔ (ƛ P) ] cpsP M ♦ ⟶ v'
lemma5' {a} {P} {v'} {M = var x} noop r2 = β r2
lemma5' {a} {P} {v'} {M = ƛ M}   noop r2 = β (tr (λ t → substT (subst0 (ƛ t)) P ⟶ v') (! lemma4) r2)
lemma5' {a} {P} {v'} {M $$ N}    noop r2 = β (tr (λ t → t ⟶ v')
    (({!lemma5' !} ∙ ap (substT _) (! cpsP-wk-naturality M)) ∙ ! subst-hom′ _ _ (cpsP (wkTm M) ♦)) r2)
lemma5' {a} {P} {v'} (ƛ r1) r2
  {-
    t ⟶ t'
    [0≔ ƛ (ƛ (cpsP t')) ] P ⟶ v'
    -------------------------------------
    [0≔ ƛ (ƛ ([ Φ ] (cpsP t)) ] P ⟶ v'

    where Φ = ext (ext [0≔ ƛ P ]) ∘ renT (map⇑ (map⇑ wkN'))
  -}
  = β ({!lemma5' {!r1!} {!!}!})
  -- (tr (λ t → substT (subst0 t) P ⟶ v') (ap ƛ_ (ap ƛ_ ({!!} ∙ ! lemma4'))) r2)
lemma5' (β r1) r2 = β (β (β {!!}))
lemma5' (r1 $$ r2) r3 = β {!!}

lemma5 : ∀{a} {M v v' : Tm a} {P : ScopeF Tm a} -> (M ⟶ v) -> (substituteOut _ (psi v) P) ⟶ v' -> cps M $$ ƛ P ⟶ v'
lemma5 r1 r2 = β (lemma5' r1 r2)

identity : ∀ {α} -> Tm α
identity = lamP λ x → var' x

theorem : ∀{a} (M : Tm a) -> app (cps M) identity ⟶ psi M
theorem M = lemma5 {M = M} {v = M} {P = var (new ◆)} noop noop
 
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
-- -}
-- -}
-- -}
-- -}
