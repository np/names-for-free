module Names where

open import Level
open import Function

open import Data.Empty 
open import Relation.Binary.PropositionalEquality


-- Let us assume union types; (poorly emulated here)
data _∪_ {v w} (V : Set v) (W : Set w) : Set (v ⊔ w) where
  left : V → V ∪ W
  right : W → V ∪ W

-- unions are functors
map-∪ : ∀{u v w}{U : Set u}{V : Set v}{W : Set w} → (V → U) →  V ∪ W → U ∪ W
map-∪ f (left x)  = left (f x)
map-∪ f (right x) = right x

-- Worlds are types, binders are quantification over any value of any type.
data Term {a} (V : Set a) : Set (suc a) where
  var : V → Term V
  abs : (∀ {W} → W → Term (V ∪ W)) → Term V
  app : Term V → Term V → Term V

-- Term is a functor (unlike PHOAS)
map : ∀{a}{U V : Set a} → (U → V) → Term U → Term V
map f (abs t)   = abs (λ x → map (map-∪ f) (t x))
map f (var x)   = var (f x)
map f (app t u) = app (map f t) (map f u)

-- Example terms
id™ : Term ⊥
id™ = abs (λ x → var (right x))

const™ : Term ⊥
const™ = abs (λ x → abs (λ y → var (left (right x))))
-- with proper union types the left/right annotations disappear

-- Weakening
wk : ∀ {a} {V W : Set a} → Term V → Term (V ∪ W)
wk = map left 
-- in particular, weakening becomes 'map id'; that is, just the identity

-- "Environment"
_⇶_ : ∀ {v w} → Set v → Set w → Set _
V ⇶ W = V → Term W

⇑_ : ∀ {a} {V W X : Set a} → V ⇶ W → (V ∪ X) ⇶ (W ∪ X)
(⇑ θ) (left x)  = wk (θ x)
(⇑ θ) (right x) = var (right x)

-- Term is also a monad
join' : ∀ {a} {V W : Set a} → V ⇶ W → Term V → Term W
join' θ (var x)   = θ x
join' θ (abs t)   = abs (λ x → join' (⇑ θ) (t x))
join' θ (app t u) = app (join' θ t) (join' θ u)

join : ∀ {V : Set _} → Term (Term V) → Term V
join = join' id

-- and substitution is then easy:
subs : ∀ {U} → (∀ {V} → V → Term V) → Term U → Term U
subs t u = join (t u)

-- Remark: because we have quantification for all types at the binder
-- level, I expect it's easy (we can follow Pouillard&Pottier) to do
-- the correctness proofs in Agda+Parametricity (no need for Kripke
-- logical relations).


-- Nbe
yak : ∀ {V} -> V ∪ Term V -> Term V
yak (left x) = var x
yak (right x) = x

app' : ∀ {V} -> Term V -> Term V -> Term V
app' (abs x) u = join' yak (x u)
app' t u = app t u

eval : ∀ {V} -> Term V -> Term V 
eval (var x) = var x
eval (abs x) = abs x
eval (app t t₁) = app' (eval t) (eval t₁)

