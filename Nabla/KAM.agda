{-# OPTIONS --type-in-type #-}
module KAM where

open import Sketch5
open Example-TmFresh


mutual
  Env : Set -> Set -> Set1
  Env v w = v -> Closure w
  
  data Closure w : Set1 where
    C : ∀ {w'} -> Tm w' -> (w' -> Closure w) -> Closure w
    Ne : Tm w -> Closure w

  data Stack w : Set1 where
    Nil : Stack w
    Cons : Closure w -> Stack w -> Stack w

instance
  postulate c-fun : Functor Closure

cenv : ∀ {v w} -> Closure w -> Env v w -> Env (v ▹ ◆) w 
cenv c ρ (old x) = ρ x
cenv c ρ (new .♦) = c

kam : ∀ {w} -> Closure w -> Stack w -> Tm w
kam (Ne v) Nil = v 
kam (Ne v) (Cons s ss) = kam (Ne (app v (kam s Nil)) ) ss 
kam (C (var x) ρ) s = kam (ρ x) s
kam (C (lam t) ρ) Nil = lam (kam (C t (λ { (old x) → wk (ρ x)  ; (new .♦) → Ne (var (new _)) })) Nil)
kam (C (lam t) ρ) (Cons s ss) = kam (C t (cenv s ρ)) ss -- nicer: unpack
kam (C (app t u) ρ) s = kam (C t ρ) (Cons (C u ρ) s)

