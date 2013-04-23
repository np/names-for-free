{-# OPTIONS --type-in-type #-}
module TmU where

open import Type
open import Function
open import Data.Sum.NP renaming (map to map-⊎; ⟦map⟧ to ⟦map-⊎⟧)
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧; ⟦⊤⟧ to ⟦𝟙⟧)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Maybe.NP
open import Data.Empty renaming (⊥ to 𝟘)
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Nat.Logical
open import Relation.Binary

open import binding-representations

conv : ∀ {A B} → A ⊎ B → Maybe A
conv (inj₁ x) = just x
conv (inj₂ _) = nothing

lam : ∀ {V} → (∀ {W} → W → Tmᴹ (V ⊎ W)) → Tmᴹ V
lam f = ƛ (mapᴹ conv (f {𝟙} _))

wz : ∀ {A B} → B → A ⊎ B
wz = inj₂

ws : ∀ {A B C} → (A → B) → A → B ⊎ C
ws f = inj₁ ∘ f

_⟨as_⟩ : ∀ {A B} → A → (A → B) → Tmᴹ B
_⟨as_⟩ x f = V (f x)

apTmᴹ' : Tmᴹ 𝟘
apTmᴹ' = lam λ f → lam λ x → f ⟨as ws wz ⟩ · x ⟨as wz ⟩

data Tm⁺ (A : ★) : ★ where
  V   : A → Tm⁺ A
  ƛ   : (∀ {B} → B → Tm⁺ (A ⊎ B)) → Tm⁺ A
  _·_ : Tm⁺ A → Tm⁺ A → Tm⁺ A

map⁺ : ∀{A B} → (A → B) → Tm⁺ A → Tm⁺ B
map⁺ f (ƛ g)   = ƛ (λ x → map⁺ (map-⊎ f id) (g x))
map⁺ f (V x)   = V (f x)
map⁺ f (t · u) = map⁺ f t · map⁺ f u

module Tm⁺⇒Tmᴹ where
    _⇑ : ∀ {A B} → (A → B) → A ⊎ 𝟙 → Maybe B
    θ ⇑ = [ just ∘ θ , const nothing ]

    [_] : ∀ {A B} → (A → B) → Tm⁺ A → Tmᴹ B
    [ θ ](V x  ) = V (θ x)
    [ θ ](ƛ f  ) = ƛ ([ θ ⇑ ](f _))
    [ θ ](t · u) = [ θ ] t · [ θ ] u

module Tmᴹ⇒Tm⁺ where
    _⇑_ : ∀ {A B C} → (A → B) → C → Maybe A → B ⊎ C
    θ ⇑ x = maybe (inj₁ ∘ θ) (inj₂ x)

    [_] : ∀ {A B} → (A → B) → Tmᴹ A → Tm⁺ B
    [ θ ](V x)   = V (θ x)
    [ θ ](ƛ f)   = ƛ (λ x → [ θ ⇑ x ] f)
    [ θ ](t · u) = [ θ ] t · [ θ ] u
