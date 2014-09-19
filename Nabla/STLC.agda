module STLC where

open import Data.Product hiding (map)
open import Data.Maybe hiding (module Eq; Eq; map)
open import Data.Nat
open import Function

open import Sketch5
open import Terms

data IVar {I : Type} {w : World} (Γ : w → I → Type)
          (b : Binder w) (i : I) : w ▹ b → I → Type where
  iold : ∀ {j x} → Γ x j → IVar Γ b i (old x) j
  inew : IVar Γ b i (new b) i


_,_↦_ : ∀ {I : Type}{w : World}
          (Γ : w → I → Type)(b : Binder w) → I → w ▹ b → I → Type
Γ , b ↦ i = IVar Γ b i

-- World extended with a fresh variable.
_,,_ : ∀ {I : Type}{w : World}(Γ : w → I → Type) → I → w ⇑ → I → Type
Γ ,, i = Γ , ♦ ↦ i

-- Types for STLC
data Ty : Type where
  _⟶_ : (S T : Ty) → Ty
  nat : Ty

-- Contexts for STLC
Cx : World → Type1
Cx α = α → Ty → Type

-- Typing derivations for STLC
infix 0 _⊢_∶_
data _⊢_∶_ {α} (Γ : Cx α) : Cx (Tm α) where
  var : ∀ {x S} → Γ x S → Γ ⊢ var x ∶ S
  lam : ∀ {t T S}
        (t⊢ : Γ ,, S ⊢ t ∶ T)
        -------------------
        → Γ ⊢ lam t ∶ S ⟶ T
  app : ∀ {t u T S}
        (t⊢ : Γ ⊢ t ∶ S ⟶ T)
        (u⊢ : Γ ⊢ u ∶ S)
        -------------------
        → Γ ⊢ app t u ∶ T
pattern _·_ t u = app t u
pattern ƛ t = lam t


-- Lifts a "renaming" to context membership proofs.
Ren⊢ : ∀ {α β}(Γ : Cx α)(Δ : Cx β)(f : α → β) → Type
Ren⊢ Γ Δ f = ∀ {T x} → Γ x T → Δ (f x) T

-- These renamings are compatible with world extension.
extRen⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{s : α → β}{b b' i}
       → Ren⊢ Γ Δ s → Ren⊢ (Γ , b ↦ i) (Δ , b' ↦ i) (map▹ b b' s)
extRen⊢ r (iold x) = iold (r x)
extRen⊢ r inew = inew

-- Renaming in a typing derivation.
ren⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{f : α → β}{t T}
     → Ren⊢ Γ Δ f
     → Γ ⊢ t ∶ T → Δ ⊢ renT f t ∶ T
ren⊢ r⊢ (var x) = var (r⊢ x)
ren⊢ r⊢ (lam d) = lam (ren⊢ (extRen⊢ r⊢) d)
ren⊢ r⊢ (app d d₁) = app (ren⊢ r⊢ d) (ren⊢ r⊢ d₁)

-- Lifts a substitution on terms as a substitution on
-- typing derivations. Context membership proofs are
-- mapped to typing derivations.
Subst⊢ : ∀ {α β}(Γ : Cx α)(Δ : Cx β)(s : α ⇶ β) → Type
Subst⊢ Γ Δ s = ∀ {T x} → Γ x T → Δ ⊢ s x ∶ T

-- These substitutions are compatible with world extension.
-- Weakening a derivation is a particular case of renaming.
extSubst⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{s : α ⇶ β}{i}
       → Subst⊢ Γ Δ s → Subst⊢ (Γ ,, i) (Δ ,, i) (ext s)
extSubst⊢ r (iold x₁) = ren⊢ iold (r x₁)
extSubst⊢ r inew = var inew

-- Substituting in a typing derivation.
subst⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{s : α ⇶ β}{t T}
         → Subst⊢ Γ Δ s
         → Γ ⊢ t ∶ T → Δ ⊢ [ s ] t ∶ T
subst⊢ r (var x) = r x
subst⊢ r (lam d) = lam (subst⊢ (extSubst⊢ r) d)
subst⊢ r (app d d₁) = app (subst⊢ r d) (subst⊢ r d₁)


subst⊢0 : ∀ {α}{u : Tm α}{Γ b T}
          → Γ ⊢ u ∶ T → Subst⊢ (Γ , b ↦ T) Γ (subst0 u)
subst⊢0 u (iold x) = var x
subst⊢0 u inew     = u



-- Type preservation: reduction preserves typing
↝-pres-⊢ : ∀ {α Γ T} {t t' : Tm α} → t ↝ t' → Γ ⊢ t ∶ T → Γ ⊢ t' ∶ T
↝-pres-⊢ β (ƛ t₁ · t₂) = subst⊢ (subst⊢0 t₂) t₁
↝-pres-⊢ ([ r ]· u) (t₁ · t₂) = ↝-pres-⊢ r t₁ · t₂
↝-pres-⊢ (u ·[ r ]) (t₁ · t₂) = t₁ · ↝-pres-⊢ r t₂
↝-pres-⊢ ƛ[ r ] (ƛ t₁) = ƛ (↝-pres-⊢ r t₁)

