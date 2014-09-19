
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

-- mutual
--   data Ne w : Set where
--     App1 : At w -> At w -> Ne w
--     App2 : At w -> Ne w -> Ne w
--     App3 : Ne w -> At w -> Ne w
--     App4 : Ne w -> Ne w -> Ne w

--   data At w : Set where
--     Var : w -> 
--     Lam : ScopeF No w -> No w

-- instance
--   postulate no-monad : Monad No

cps : ∀ {a} -> Tm a -> ScopeF Tm a -> Tm a
cps (var x) k = load x <$> k
cps (lam t) k = lam (pack Tm λ x → lam (pack Tm λ k' → cps ( wk (atVar Tm t x) )  (var' k')))
cps (app e1 e2) k = cps e1 (pack Tm λ m →
                    cps (wk e2) (pack Tm λ n →
                    app (app (var' m) (var' n)) (lam (pack Tm (λ x' → atVar' Tm k x')))))


