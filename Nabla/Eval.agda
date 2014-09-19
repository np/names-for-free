module Eval where

open import Sketch5
open import Terms



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
