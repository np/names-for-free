module nbe where

open import Function
open import Data.Maybe.NP
open import Data.Nat.NP
open import Data.Bool
open import Data.Unit using (⊤)
open import binding-representations

open import nbe-terms {- HERE we are importing non-strictly
                         positive data types (Sem and Neu) -}

app : ∀ {A} → Sem A → Sem A → Sem A
app (ƛ f) s = f s
app (N n) s = N (n · s)

evalᴴ : Tmᴴ₀ → {A : Set} → Sem A
evalᴴ f = f ƛ app

reifyᴴ : ∀ {Exp} → Sem Exp → Tmᴴ Exp
reifyᴴ s lam app = sem s
 module Reifyᴴ where
  sem : Sem _ → _
  neu : Neu _ → _

  sem (ƛ f) = lam λ x → sem (f (N (V x)))
  sem (N n) = neu n

  neu (V v)   = v
  neu (n · d) = app (neu n) (sem d)

normᴴ : Tmᴴ₀ → Tmᴴ₀
normᴴ t = reifyᴴ (evalᴴ t)

module examplesᴴ where
    t1ᴴ : Tmᴴ₀
    t1ᴴ lam _∙_ = (lam λ x → lam λ y → x ∙ y) ∙ (lam λ x → x)

    t2ᴴ : Tmᴴ₀
    t2ᴴ lam _∙_ = lam λ z → ((lam λ x → lam λ y → x ∙ y) ∙ z) ∙ (lam λ x → lam λ y → x ∙ y)

evalᴾ : {A : Set} → Tmᴾ (Sem A) → Sem A
evalᴾ (V v)   = v
evalᴾ (t · u) = app (evalᴾ t) (evalᴾ u)
evalᴾ (ƛ f)   = ƛ λ x → evalᴾ (f x)

reifyᴾ : ∀ {Exp} → Sem Exp → Tmᴾ Exp
reifyᴾ (ƛ f) = ƛ λ x → reifyᴾ (f (N (V x)))
reifyᴾ (N n) = neu n
 module Reifyᴾ where
  neu : Neu _ → _
  neu (V v)   = V v
  neu (n · d) = neu n · reifyᴾ d

normᴾ : Tmᴾ₀ → Tmᴾ₀
normᴾ t = reifyᴾ (evalᴾ t)

module examplesᴾ where
    t1ᴾ : Tmᴾ₀
    t1ᴾ = (ƛ λ x → ƛ λ y → V x · V y) · (ƛ λ x → V x)

    t2ᴾ : Tmᴾ₀
    t2ᴾ = ƛ λ z → ((ƛ λ x → ƛ λ y → V x · V y) · V z) · (ƛ λ x → ƛ λ y → V x · V y)

idᴾ : Tmᴾ₀
idᴾ = parseTmᴾ "λx.x"
trueᴾ : Tmᴾ₀
trueᴾ = parseTmᴾ "λx.λ_.x"
falseᴾ : Tmᴾ₀
falseᴾ = parseTmᴾ "λ_.λx.x"
pairᴾ : Tmᴾ₀
pairᴾ = parseTmᴾ "λx.λy.λf.f x y"
fstᴾ : Tmᴾ₀
fstᴾ = parseTmᴾ "λtrue.λp.p true" · trueᴾ
  -- = parseTmᴾ "λp.p (λx.λ_.x)"
sndᴾ : Tmᴾ₀
sndᴾ = parseTmᴾ "λfalse.λp.p false" · falseᴾ
  -- = parseTmᴾ "λp.p (λ_.λx.x)"
uncurryᴾ : Tmᴾ₀
uncurryᴾ = parseTmᴾ "λtrue.λfalse.λf.λp.f (p true) (p false)" · trueᴾ · falseᴾ
      -- = parseTmᴾ "λf.λp.f (p (λx.λ_.x)) (p (λ_.λx.x))"
appᴾ : Tmᴾ₀
appᴾ = parseTmᴾ "λf.λx.f x"
compᴾ : Tmᴾ₀
compᴾ = parseTmᴾ "λf.λg.λx.f (g x)"

-- ℕ = ∀ {α} → (α → α) → (α → α)
zeroᴾ : Tmᴾ₀
zeroᴾ = falseᴾ -- "λf.λx.x"
sucᴾ  : Tmᴾ₀
sucᴾ  = parseTmᴾ "λn.λf.λx.n f (f x)" -- λn.λf.n f ∘ f
addᴾ  : Tmᴾ₀
addᴾ  = parseTmᴾ "λsuc.λm.m suc" · sucᴾ
multᴾ : Tmᴾ₀
multᴾ = parseTmᴾ "λzero.λadd.λm.λn.m (add n) zero" · zeroᴾ · addᴾ

_ℕᴾ : ℕ → Tmᴾ₀
n ℕᴾ = ƛ λ x → ƛ λ y → fold (V y) (_·_ (V x)) n

2+1ᴾ : Tmᴾ₀
2+1ᴾ = addᴾ · 2 ℕᴾ · 1 ℕᴾ

3×4ᴾ : Tmᴾ₀
3×4ᴾ = multᴾ · 3 ℕᴾ · 4 ℕᴾ

count-app-right : Tmᴾ ⊤ → ℕ
count-app-right (t · u) = suc (count-app-right u)
count-app-right _       = zero

Tmᴾ⊤⇒ℕ : Tmᴾ ⊤ → ℕ
Tmᴾ⊤⇒ℕ (ƛ f) with f _
Tmᴾ⊤⇒ℕ (ƛ f)    | ƛ g = count-app-right (g _)
Tmᴾ⊤⇒ℕ (ƛ f)    | _   = zero
Tmᴾ⊤⇒ℕ _ = zero

Tmᴾ₀⇒ℕ : Tmᴾ₀ → ℕ
Tmᴾ₀⇒ℕ t = Tmᴾ⊤⇒ℕ t

normᴾℕ = Tmᴾ₀⇒ℕ ∘ normᴾ

succ : ℕ → ℕ
succ x = normᴾℕ (sucᴾ · x ℕᴾ)

add : ℕ → ℕ → ℕ
add x y = normᴾℕ (addᴾ · x ℕᴾ · y ℕᴾ)

mul : ℕ → ℕ → ℕ
mul x y = normᴾℕ (multᴾ · x ℕᴾ · y ℕᴾ)

test2*4 : T (mul 2 4 == 8)
test2*4 = _
