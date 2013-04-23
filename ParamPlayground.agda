{-# OPTIONS --type-in-type #-}
module ParamPlayground where

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

Subst : (A : ★) → ⟦★⟧ A A
Subst A x y = ∀ (P : A → ★) → P x → P y

⟦ℕ⟧-subst : ⟦ℕ⟧ ⇒ Subst ℕ
⟦ℕ⟧-subst zero    P = id
⟦ℕ⟧-subst (suc n) P = ⟦ℕ⟧-subst n (P ∘ suc)

subst⇒≡ : ∀ {A} → Subst A ⇒ _≡_
subst⇒≡ {A} {x} A-subst = A-subst (_≡_ x) refl

→-refl : ∀ {A : ★} (Aᵣ : ⟦★⟧ A A) (subst : Aᵣ ⇒ Subst A) f → (Aᵣ ⟦→⟧ ⟦ℕ⟧) f f
→-refl Aᵣ A-subst f {x} xᵣ = A-subst xᵣ (λ y → ⟦ℕ⟧ (f x) (f y)) ⟦ℕ⟧ᵉ.refl


{-
data O : ★ where
  zero : O
  suc  : O → O
  lim  : (ℕ → O) → O

data Or : ⟦★⟧ O O where
  zero : Or zero zero
  suc  : (Or ⟦→⟧ Or) suc suc
  lim  : ((⟦ℕ⟧ ⟦→⟧ Or) ⟦→⟧ Or) lim lim

Or-refl : (x : O) → Or x x
Or-refl zero = zero
Or-refl (suc x) = suc (Or-refl x)
Or-refl (lim f) = {!!} -- lim (helper f 0 (Or-refl (f 0)))
  where helper : ∀ k (0r : Or (f k) (f k)) {n0 n1} (nr : ⟦ℕ⟧ n0 n1) → Or (f (n0 + k)) (f (n1 + k))
        helper k 0r zero     = 0r
        helper k 0r (suc nr) = helper (suc k) {!!} nr
        -}
