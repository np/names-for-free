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

module _ {F : Set -> Set} {{F : Monad F}} where
  open Monad F public

appl : ∀ {a} -> No a -> No a -> No a
appl (Neu x) u = Neu (App x u)
appl (Lam t) u = substituteOut _ u t

norm : ∀ {w} -> Tm w -> No w
norm (var x) = return x
norm (lam x) = Lam (norm x)
norm (app t u) = appl (norm t) (norm u)
