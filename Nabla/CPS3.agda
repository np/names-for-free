module CPS3 where

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
cpsP : ∀ {a} -> Tm a -> ScopeP Tm a -> Tm a
cpsP (var x) k = load x <$> k ♦
cpsP (lam t) k = letP
                  (lamP λ x →
                   lamP λ k' →
                   cpsP (wk (atVar' t x)) (λ z → var' k')) k
cpsP (e1 $$ e2) k = cpsP e1 λ m →
                    cpsP (wk e2) λ n →
                    (var' m $$ var' n) $$ (lamP (λ x' → atVar' (k ♦) x'))

cps : ∀ {a} -> Tm a -> Tm a
cps t = cpsP t (λ x → var' x)

-- TODO import from CPS2 ...
