module Eval where

open import Sketch5
open Example-TmFresh


mutual
  data Ne w : Set where
    Var : w -> Ne w
    App : Ne w -> No w -> Ne w
    
  data No w : Set where
    Neu : Ne w -> No w
    Lam : ScopeF No w -> No w

instance
  postulate no-monad : Monad No


appl : ∀ {a} -> No a -> No a -> No a
appl = {!!}

-- norm : ∀ {w} -> Tm w -> No w
-- norm (Var x) = return x
-- norm (App t u)
