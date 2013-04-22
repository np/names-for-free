{-# OPTIONS  --type-in-type #-}
module NamesRel where

open import Type
open import Function
open import Data.Sum.NP renaming (map to map-⊎)
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧)
open import Level
open import Relation.Binary.PropositionalEquality
--open import Names

module V1 where

    data Term (V : ★) : ★ where
      var : V → Term V
      abs : (∀ {W} → W → Term (V ⊎ W)) → Term V
      app : Term V → Term V → Term V
 
    map : ∀{U V} → (U → V) → Term U → Term V
    map f (abs t)   = abs (λ x → map (map-⊎ f id) (t x))
    map f (var x)   = var (f x)
    map f (app t u) = app (map f t) (map f u)

    data ⟦Term⟧ {V₁ V₂} (Vᵣ : ⟦★⟧ V₁ V₂) : Term V₁ → Term V₂ → ★ where
      ⟦var⟧ : (Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ) var var
      ⟦abs⟧ : ((∀⟨ Wᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Wᵣ ⟦→⟧ ⟦Term⟧ (Vᵣ ⟦⊎⟧ Wᵣ)) ⟦→⟧ ⟦Term⟧ Vᵣ) abs abs
      ⟦app⟧ : (⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ) app app

    mapR : (∀⟨ UR ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ VR ∶ ⟦★⟧ ⟩⟦→⟧  (UR ⟦→⟧ VR) ⟦→⟧ ⟦Term⟧ UR ⟦→⟧ ⟦Term⟧ VR) map map
    mapR UR VR fr (⟦var⟧ xᵣ) = ⟦var⟧ (fr xᵣ)
    mapR UR VR fr (⟦abs⟧ xᵣ) = ⟦abs⟧ (λ {W1} {W2} Wᵣ {w1} {w2} wᵣ → mapR (UR ⟦⊎⟧ Wᵣ) (VR ⟦⊎⟧ Wᵣ) (⟦map⟧ _ _ _ _ fr id) (xᵣ Wᵣ wᵣ))
    mapR UR VR fr (⟦app⟧ tr tr₁) = ⟦app⟧ (mapR UR VR fr tr) (mapR UR VR fr tr₁)

    IdTerm = ∀ {V} → Term V → Term V
    ⟦IdTerm⟧ : ⟦★⟧ IdTerm IdTerm
    ⟦IdTerm⟧ = ∀⟨ Vᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ⟦Term⟧ Vᵣ ⟦→⟧ ⟦Term⟧ Vᵣ

    
    ⟦Term⟧-refl : ∀ {V} -> (t : Term V) -> ⟦Term⟧ _≡_ t t
    ⟦Term⟧-refl = {!!}

    -- data RelOf {A B : ★} (f : A → B) : A → B → ★ where
    --  relOf : ∀ {x} → RelOf f x (f x)

    RelOf : ∀ {A B : ★} (f : A → B) -> A → B → ★
    RelOf f x y = y ≡ f x 

    module ⟦Term⟧-map
                (ext : ∀ {V W X} → (V → W) → (V ⊎ X → W ⊎ X)) where
                -- (⟦ext⟧ : ∀ {W₁ W₂} (Wᵣ : ⟦★⟧ W₁ W₂) (φ : ?) → RelOf φ ⟦∪⟧ Wᵣ → RelOf (ext φ)) where
        proof : ∀ {V W} (φ : V → W) t → ⟦Term⟧ (RelOf φ) (map id t) (map φ t)
        proof φ t = mapR {!!} (RelOf φ) {id} {φ} {!!} {t} {t} {!!}
{-
        proof _ (var _)   = ⟦var⟧ refl
        proof φ (abs f)   = ⟦abs⟧ (λ {W1} {W2} Wᵣ {w1} {w2} wᵣ → {!proof (ext φ) (f w1)!})
        proof φ (app t u) = ⟦app⟧ (proof φ t) (proof φ u)
-}
    module TermOp (f  : IdTerm)
                  (fᵣ : ⟦IdTerm⟧ f f)
                  {V W}
                  (φ  : V → W)
                  (t  : Term V) where
      lem : ⟦Term⟧ {!!} (map φ (f t)) (f (map φ t))
      lem = {!!}
      -- lem : map φ (f t) ≡ f (map φ t)

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
