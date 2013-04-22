{-# OPTIONS --type-in-type #-}
module NamesRel where

open import Type
open import Function
open import Data.Sum.NP renaming (map to map-⊎)
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧)
open import Level
--open import Names

module Lib {World : ★}
           (⟦World⟧ : ⟦★⟧ World World)
           {Name : World → ★}
           (⟦Name⟧ : (⟦World⟧ ⟦→⟧ ⟦★⟧) Name Name)
           {_∪_ : World → World → World}
           (_⟦∪⟧_ : (⟦World⟧ ⟦→⟧ ⟦World⟧ ⟦→⟧ ⟦World⟧) _∪_ _∪_)
           (map-∪ : ∀ {V W X} → (Name V → Name W) → Name (V ∪ X) → Name (W ∪ X)) where
    -- {-
    -- Worlds are types, binders are quantification over any value of any type.
    data Term (V : World) : ★ where
      var : Name V → Term V
      abs : (∀ {W} → Name W → Term (V ∪ W)) → Term V
      app : Term V → Term V → Term V

    -- Term is a functor (unlike PHOAS)
    map : ∀{U V} → (Name U → Name V) → Term U → Term V
    map f (abs t)   = abs (λ x → map (map-∪ f) (t x))
    map f (var x)   = var (f x)
    map f (app t u) = app (map f t) (map f u)
    -- -}

    {-
    data ⟦Term⟧ {a₁ a₂ aᵣ} {V₁ : Set a₁} {V₂ : Set a₂} (Vᵣ : ⟦Set⟧ aᵣ V₁ V₂) : Term V₁ → Term V₂ → Set (suc aᵣ) where
      ⟦var⟧ : (Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ) var var
      ⟦abs⟧ : ((∀⟨ Wᵣ ∶ ⟦Set⟧ aᵣ ⟩⟦→⟧ Wᵣ ⟦→⟧ ⟦Term⟧ (Vᵣ ⟦⊎⟧ Wᵣ)) ⟦→⟧ ⟦Term⟧ Vᵣ) abs abs
      ⟦app⟧ : (⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ) app app
    -}
    data ⟦Term⟧ {V₁ V₂} (Vᵣ : ⟦World⟧ V₁ V₂) : Term V₁ → Term V₂ → ★ where
      ⟦var⟧ : (⟦Name⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ) var var
      ⟦abs⟧ : ((∀⟨ Wᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ Wᵣ ⟦→⟧ ⟦Term⟧ (Vᵣ ⟦∪⟧ Wᵣ)) ⟦→⟧ ⟦Term⟧ Vᵣ) abs abs
      ⟦app⟧ : (⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ) app app

    IdTerm = ∀ {V} → Term V → Term V
    ⟦IdTerm⟧ : ⟦★⟧ IdTerm IdTerm
    ⟦IdTerm⟧ = ∀⟨ Vᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ

module LibProofs where
    World : ★
    World = ★
    Name : World → ★
    Name α = {!!}
    ⟦World⟧ : ⟦★⟧ World World
    ⟦World⟧ α β = {!!}
    ⟦Name⟧ : (⟦World⟧ ⟦→⟧ ⟦★⟧) Name Name
    ⟦Name⟧ αᵣ βᵣ = {!!}
    _∪_ : World → World → World
    α ∪ β = {!!}
    _⟦∪⟧_ : (⟦World⟧ ⟦→⟧ ⟦World⟧ ⟦→⟧ ⟦World⟧) _∪_ _∪_
    αᵣ ⟦∪⟧ βᵣ = {!!}
    map-∪ : ∀ {V W X} → (Name V → Name W) → Name (V ∪ X) → Name (W ∪ X)
    map-∪ = {!!}

  {-
    open Lib ⟦World⟧ ⟦Name⟧ _⟦∪⟧_ map-∪
    _∪_ = _⊎_
    _⟦∪⟧_ : (⟦★⟧ ⟦→⟧ ⟦★⟧ ⟦→⟧ ⟦★⟧) _∪_ _∪_
    _⟦∪⟧_ = {!!}

    data RelOf {A B : ★} (f : A → B) : A → B → ★ where
      relOf : ∀ {x} → RelOf f x (f x)

    module ⟦Term⟧-map
                (ext : ∀ {V W X} → (V → W) → (V ∪ X → W ∪ X)) where
                -- (⟦ext⟧ : ∀ {W₁ W₂} (Wᵣ : ⟦★⟧ W₁ W₂) (φ : ?) → RelOf φ ⟦∪⟧ Wᵣ → RelOf (ext φ)) where
        proof : ∀ {V W} (φ : V → W) t → ⟦Term⟧ (RelOf φ) t (map φ t)
        proof _ (var _)   = ⟦var⟧ relOf
        proof φ (abs f)   = ⟦abs⟧ (λ Wᵣ wᵣ → {!proof (ext φ)!})
        proof φ (app t u) = ⟦app⟧ (proof φ t) (proof φ u)

    module TermOp (f  : IdTerm)
                  (fᵣ : ⟦IdTerm⟧ f f)
                  {V W}
                  (φ  : V → W)
                  (t  : Term V) where
      lem : ⟦Term⟧ {!!} (map φ (f t)) (f (map φ t))
      lem = {!!}
      -- lem : map φ (f t) ≡ f (map φ t)
-- -}
-- -}
-- -}
-- -}
-- -}
