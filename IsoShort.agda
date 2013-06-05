-- Proof that forall functor F, (∀ {A} → A → F A) ≅ F 𝟙

open import Type
open import Function.NP
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧; ⟦⊤⟧ to ⟦𝟙⟧)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Unit renaming (⊤ to 𝟙)

module IsoShort
         {F  : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         (mapF-id : ∀ {A} → mapF {A} id ≡ id)
         where

  f : (∀ {A} → A → F A) → F 𝟙
  f α = α tt
  
  f⁻¹ : F 𝟙 → (∀ {A} → A → F A)
  f⁻¹ t b = mapF (λ _ → b) t

  module _
         {X  : ★}
         {Xᵣ : ⟦★⟧ X X}
         {t u : F X} where
    subst-mapF-id : Fᵣ Xᵣ t (mapF id u) → Fᵣ Xᵣ t u
    subst-mapF-id = subst (λ C → Fᵣ Xᵣ t (C u)) mapF-id

  ST∘TS-id : ∀ {t : F 𝟙} (tᵣ : Fᵣ ⟦𝟙⟧ t t) → Fᵣ ⟦𝟙⟧ (f (f⁻¹ t)) t
  ST∘TS-id = subst-mapF-id ∘ mapFᵣ _ _ _

  module _
         (α  : ∀ {X} → X → F X)
         (αᵣ : (∀⟨ Xᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Xᵣ) α α)
         (X  : ★)
         (Xᵣ : ⟦★⟧ X X)
         (x  : X)
         (xᵣ : Xᵣ x x)
         where

    TS∘ST-id : Fᵣ Xᵣ ((f⁻¹ ∘ f) α x) (α x)
    TS∘ST-id = subst-mapF-id (mapFᵣ _ _ id (αᵣ _ xᵣ))
