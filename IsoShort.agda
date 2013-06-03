-- Proof that forall functor F, (∀ {A} → A → F A) ≅ F 𝟙

open import Type
open import Function.NP
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧; ⟦⊤⟧ to ⟦𝟙⟧)
open import Data.Unit renaming (⊤ to 𝟙)

module IsoShort
         {F  : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         where

  f : (∀ {A} → A → F A) → F 𝟙
  f α = α tt
  
  f⁻¹ : F 𝟙 → (∀ {A} → A → F A)
  f⁻¹ t b = mapF (λ _ → b) t

  module _
         {X  : ★}
         (Xᵣ : ⟦★⟧ X X) where
    R : (t u : F X) → ★
    R t u = Fᵣ Xᵣ t (mapF id u)

  ST∘TS-id : ∀ {t : F 𝟙} (tᵣ : Fᵣ ⟦𝟙⟧ t t) → R ⟦𝟙⟧ (f (f⁻¹ t)) t
  ST∘TS-id = mapFᵣ _ _ _

  module _
         (α  : ∀ {X} → X → F X)
         (αᵣ : (∀⟨ Xᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Xᵣ) α α)
         (X  : ★)
         (Xᵣ : ⟦★⟧ X X)
         (x  : X)
         (xᵣ : Xᵣ x x)
         where

        TS∘ST-id : R Xᵣ ((f⁻¹ ∘ f) α x) (α x)
        TS∘ST-id = mapFᵣ _ _ id (αᵣ _ xᵣ)
