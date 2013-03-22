{-# OPTIONS --no-positivity-check --no-termination-check #-}
-- starting from nbe-hoas
module nbe-hoas3 where

open import Function

-- Open HOAS terms
OTm : Set → Set
OTm A = (lam : (A → A) → A) →
        (app : A → A → A) → A

-- Close HOAS terms
Tm : Set₁
Tm = ∀ {A} → OTm A

data Sem v : Set where
  L : (Sem v → Sem v) → Sem v
  V : v → Sem v
  A : Sem v → Sem v → Sem v

eval : {v : Set} → Tm → Sem v
eval {v} f = f L app′ where
  app′ : Sem v → Sem v → Sem v
  app′ (L f) x = f x
  app′ f     x = A f x

reify : ∀ {Exp} → Sem Exp → OTm Exp
reify s lam app = go s where
  go : Sem _ → _
  go (L f)   = lam $ go ∘ f ∘ V
  go (V v)   = v
  go (A n d) = app (go n) (go d)

norm : Tm → Tm
norm t = reify (eval t)

t₁ : Tm
t₁ lam _·_ = (lam λ x → lam λ y → x · y) · (lam λ x → x)

t₂ : Tm
t₂ lam _·_ = lam λ z → ((lam λ x → lam λ y → x · y) · z) · (lam λ x → lam λ y → x · y)
