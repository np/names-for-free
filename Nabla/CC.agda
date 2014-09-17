module CC where

open import Data.List
open import Data.Product hiding (map)
open import Data.Maybe hiding (module Eq; Eq; map)
open import Data.Nat

open import Sketch5
open Example-TmFresh

data LC (α : World) : Set where
  var : α → LC α
  app : LC α → LC α → LC α
  closureS : (NablaS _ λ venv →
              NablaS _ λ vx →
              LC (Zero ▹ venv ▹ vx))
             → LC α → LC α
  tuple : List (LC α) → LC α
  index : LC α → ℕ → LC α
  let-openS : LC α →
             (NablaS _ λ vf →
              NablaS _ λ venv →
              LC (α ▹ vf ▹ venv))
             → LC α

infixl 5 _$$_
_$$_ : ∀ {α : World} → LC α → LC α → LC α
_$$_ = app

let-open : ∀ {α} → LC α → (∀ vf venv →
                   LC (α ▹ vf ▹ venv)) → LC α
let-open t f = let-openS t (♦ , ♦ , f ♦ ♦)

closure : ∀ {α} → (∀ vx venv → -- Rem: I had to change the order of quantifiers since they now depend on each other.
           LC (Zero ▹ vx ▹ venv)) →
           LC α → LC α
closure f t = closureS (♦ , ♦ , f ♦ ♦) t
 
varLC : ∀ {w w'}(b : Binder w){{s : b ∈ w'}} → LC w'
varLC b = var (name' b)
 
idx : ∀ {w a} (v : Binder w) {{_ : v ∈ a}} → ℕ → LC a
idx env = index (varLC env)

record Eq (A : Set) : Set where
  field
    _=?_ : A → A → Bool

nub : ∀ {A : Set} {{_ : Eq A}} → List A → List A
nub = {!!}

free-vars : ∀ {A : Set} → Tm A → List A
free-vars = {!!}

LC-Monad : Monad LC
LC-Monad = {!!}

-- Kleisli arrows
Kl : (m : Set → Set) (v w : Set) → Set
Kl m v w = v → m w

renLC : ∀ {α β} → (α → β) → LC α → LC β
renLCL : ∀ {α β} → (α → β) → List (LC α) → List (LC β)

renLC f (var x) = var (f x)
renLC f (app t u) = app (renLC f t) (renLC f u)
renLC f (closureS t u) = closureS t (renLC f u)
renLC f (tuple ts) = tuple (renLCL f ts)
renLC f (index t i) = index (renLC f t) i
renLC f (let-openS t (vf , venv , u)) =
  let-open (renLC f t) λ vf' venv' →
    renLC (map▹ venv venv' (map▹ vf vf' f)) u

renLCL f [] = []
renLCL f (t ∷ ts) = renLC f t ∷ renLCL f ts

wkLC : ∀ {α β} {{i : α ⇉ β}} → LC α → LC β
wkLC = renLC wkN'

{-
-- '(▹ v)' is a functor in the category of Kleisli arrows
lift : ∀ {tm a b v v'} {{_ : Monad tm}} → Kl tm a b → Kl tm (a ▹ v) (b ▹ v')
lift θ (old x) = old <$> θ x -- wk (θ x)
  where open Monad …
lift θ (new x) = return (new _)
  where open Monad …
  -}

lift : ∀ {a b v v'} → Kl LC a b → Kl LC (a ▹ v) (b ▹ v')
lift θ (old x) = wkLC (θ x)
lift θ (new x) = var (new _)

module LC-monad where

  _>>=L_ : ∀ {A B} → List (LC A) → (A → LC B) → List (LC B)
  _>>=_ : ∀ {A B} → LC A → (A → LC B) → LC B

  var x >>= θ = θ x
  closureS c env >>= θ = closureS c (env >>= θ)
  let-openS t (_ , _ , g) >>= θ =
    let-openS (t >>= θ) (♦ , ♦ , g >>= lift (lift θ))
  tuple ts >>= θ = tuple (ts >>=L θ)
  index t i >>= θ = index (t >>= θ) i
  app t u >>= θ = app (t >>= θ) (u >>= θ)

  [] >>=L θ = []
  (t ∷ ts) >>=L θ = t >>= θ ∷ ts >>=L θ


elemIndex : ∀ {A : Set} {{_ : Eq A}} → A → List A → Maybe ℕ
elemIndex = {!!}

fromJust : ∀ {A : Set} → A → Maybe A → A
fromJust dflt (just x) = x
fromJust dflt nothing = dflt

dummy-idx : ℕ
dummy-idx = {!!}

cc : ∀ {w} {{_ : Eq w}} → Tm w → LC w
cc (var x) = var x
cc {w} {-t0@-}(lam f) = 
  let yn = nub (free-vars (lam f))
      bindAll : ∀ {w'} (env : Binder w') → w → LC (w' ▹ env)
      bindAll = \env z → idx env (fromJust dummy-idx (elemIndex z yn))
      open Monad LC-Monad hiding (map)
  in closure (λ x env → cc {!f x!} >>= {!lift (bindAll env)!})
          (tuple (map var yn))
  
cc (app e1 e2) = 
  let-open (cc e1)
           (λ f x → varLC f $$ wkLC (cc e2) $$ varLC x)

  
-- -}
-- -}
-- -}
-- -}
-- -}
