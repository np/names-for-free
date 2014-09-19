{-# OPTIONS --type-in-type #-}
module KAM where

open import Sketch5
open import Data.List
open import Terms

mutual
  Env : Set → Set → Set1
  Env v w = v → Closure w
  
  data Closure w : Set1 where
    _/_ : ∀ {w'} → Tm w' → Env w' w → Closure w
    ne  : Tm w → Closure w

  Stack : World → Set1
  Stack w = List (Closure w)

instance
  postulate c-fun : Functor Closure

cenv : ∀ {v w} → Closure w → Env v w → Env (v ▹ ◆) w
cenv c ρ (old x) = ρ x
cenv c ρ (new .♦) = c

ext-env : ∀ {v w} (s : Env v w) → Env (v ⇑) (w ⇑)
ext-env f (old x)  = wk (f x)
ext-env f (new ._) = ne (var (new ♦))

kam : ∀ {w} → Closure w → Stack w → Tm w
kam (ne v) [] = v
kam (ne v) (s ∷ ss) = kam (ne (app v (kam s [])) ) ss
kam (var x   / ρ) s = kam (ρ x) s
kam (lam t   / ρ) [] = lam (kam (t / ext-env ρ) [])
kam (lam t   / ρ) (s ∷ ss) = kam (t / cenv s ρ) ss -- nicer: unpack
kam (app t u / ρ) s = kam (t / ρ) (u / ρ ∷ s)

