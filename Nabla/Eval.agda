module Eval where

open import Sketch5
open import Terms


infix 0 _↝_
data _↝_ {α} : (t u : Tm α) → Type where
  β     : ∀ {t u} → app (lam t) u ↝ [0≔ u ] t
  [_]·_ : ∀ {t t'}(r : t ↝ t') u → app t u ↝ app t'  u
  _·[_] : ∀ {t t'} u (r : t ↝ t') → app u t ↝ app u t'
  ƛ[_]  : ∀ {t t'}(r : t ↝ t') → lam t ↝ lam t'

mutual
  data Ne w : Set where
    Var : w -> Ne w
    App : Ne w -> No w -> Ne w
    
  data No w : Set where
    Neu : Ne w -> No w
    Lam : ScopeF No w -> No w

_>>='_ : ∀ {a b} -> Ne a -> (a -> No b) -> No b
_>>='_ = {!!}

instance
  no-monad : Monad No
  no-monad = record
               { return = λ {A} z → Neu (Var z)
               ; _>>=_ = λ { (Neu (Var x)) θ → θ x
                           ; (Neu (App t u)) θ → {!!} ; (Lam x) θ → {!!} }
               ; bind-assoc = {!!}
               ; right-id = {!!}
               ; left-id = {!!}
               }


appl : ∀ {a} -> No a -> No a -> No a
appl (Neu x) u = Neu (App x u)
appl (Lam t) u = substituteOut _ u t

norm : ∀ {w} -> Tm w -> No w
norm (var x) = return x
norm (lam x) = Lam (norm x)
norm (app t u) = appl (norm t) (norm u)
