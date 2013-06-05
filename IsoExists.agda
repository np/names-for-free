-- Proof that forall functor F, (∃[ A ] A × F A) ≅ F 𝟙

open import Type
open import Function.NP
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧; ⟦⊤⟧ to ⟦𝟙⟧)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Product.NP

module IsoExists
         {F  : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         (mapF-id : ∀ {A} → mapF {A} id ≡ id)
         where

  f : (∃[ A ] A × F A) → F 𝟙
  f (_ , _ , x) = mapF _ x
  
  f⁻¹ : F 𝟙 → (∃[ A ] A × F A)
  f⁻¹ t = _ , _ , t

  module _
         {X₁ X₂ : ★}
         {Xᵣ    : ⟦★⟧ X₁ X₂}
         {t₁    : F X₁}
         {t₂    : F X₂} where
    subst-mapF-id : Fᵣ Xᵣ t₁ (mapF id t₂) → Fᵣ Xᵣ t₁ t₂
    subst-mapF-id = subst (λ C → Fᵣ Xᵣ t₁ (C t₂)) mapF-id

  ST∘TS-id : ∀ {t : F 𝟙} (tᵣ : Fᵣ ⟦𝟙⟧ t t) → Fᵣ ⟦𝟙⟧ (f (f⁻¹ t)) t
  ST∘TS-id = subst-mapF-id ∘ mapFᵣ _ _ _

  ℛ∃F : (e₁ e₂ : ∃[ A ] A × F A) → ★
  ℛ∃F (_ , _ , t₁) (_ , _ , t₂) = Fᵣ (λ _ _ → 𝟙) t₁ t₂

  TS∘ST-id : ∀ (t  : ∃[ A ] A × F A)
               (tᵣ : (⟦∃⟧[ Aᵣ ] Aᵣ ⟦×⟧ Fᵣ Aᵣ) t t)
             → ℛ∃F (f⁻¹ (f t)) t
  TS∘ST-id t (_ , _ , tᵣ) = subst-mapF-id (mapFᵣ _ _ _ tᵣ)
