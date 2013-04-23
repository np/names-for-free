{-# OPTIONS --type-in-type #-}
module Iso where

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


module Iso
         {F : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         (Fᵣ-refl : ∀ {A} {Aᵣ : Rel A _} → Reflexive Aᵣ → Reflexive (Fᵣ Aᵣ))
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         --(mapF-id : ∀ {A₁ A₂} (Aᵣ : ⟦★⟧ A₁ A₂) → (Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) id (mapF id))
         --(mapF-id : ∀ {A₁ A₂} (Aᵣ : ⟦★⟧ A₁ A₂) → (Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id)
         {A}
         (Aᵣ : ⟦★⟧ A A)
         (Aᵣ-refl : Reflexive Aᵣ) where
  Aᵣ+1 = Aᵣ ⟦⊎⟧ ⟦𝟙⟧
  S = ∀ {B} → B → F (A ⊎ B)
  ⟦S⟧ = ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Bᵣ ⟦→⟧ Fᵣ (Aᵣ ⟦⊎⟧ Bᵣ)
  T = F (A ⊎ 𝟙)
  ⟦T⟧ = Fᵣ Aᵣ+1
  ⟦T⟧-refl : Reflexive ⟦T⟧
  ⟦T⟧-refl = Fᵣ-refl (⟦⊎⟧-refl _ Aᵣ-refl _ _)
  ST : S → T
  ST s = s tt
  ⟦ST⟧ : (⟦S⟧ ⟦→⟧ ⟦T⟧) ST ST
  ⟦ST⟧ sᵣ = sᵣ _ ⟦tt⟧
  TS : T → S
  TS t {B} b = mapF (map-⊎ id (const b)) t
  ⟦TS⟧ : (⟦T⟧ ⟦→⟧ ⟦S⟧) TS TS
  ⟦TS⟧ tᵣ Bᵣ bᵣ = mapFᵣ _ _ (⟦map-⊎⟧ _ _ _ _ id (const bᵣ)) tᵣ
  TST = ST ∘ TS
  ⟦TST⟧ = λ {t₁ t₂} (tᵣ : ⟦T⟧ t₁ t₂) → ⟦ST⟧ (⟦TS⟧ tᵣ)
  -- mapF id ≡ id
  TST' : ∀ {t} → Fᵣ Aᵣ+1 (ST (TS t)) (mapF (map-⊎ id id) t)
  TST' = ⟦TST⟧ ⟦T⟧-refl
  STS = TS ∘ ST
  ⟦STS⟧ = λ {t₁ t₂ : S} (tᵣ : ⟦S⟧ t₁ t₂) → (λ {x} {y} → ⟦TS⟧ (⟦ST⟧ tᵣ) {x} {y})
  -- UNFINISHED
  {-
  ⟦S⟧-refl : Reflexive ⟦S⟧
  ⟦S⟧-refl {s} {B₁} {B₂} Bᵣ {b₁} {b₂} bᵣ = {!!}
  bla : ∀ (s : S) → Fᵣ Aᵣ+1 (TS (ST s) tt) (mapF (map-⊎ id (const tt)) (s tt))
  bla s = ⟦STS⟧ (⟦S⟧-refl {s}) ⟦𝟙⟧ {tt} _
  bla' : ∀ (s : S) {B} (b : B) → Fᵣ (Aᵣ ⟦⊎⟧ {!!}) (TS (ST s) b) (mapF (map-⊎ id (const b)) (s b))
  bla' s {B} b = {!⟦STS⟧ (⟦S⟧-refl {s}) ? {b} _ !}
  STS' : ∀ (x : S) {B} (Bᵣ : ⟦★⟧ B B) {b} (bᵣ : Bᵣ b b) → Fᵣ (Aᵣ ⟦⊎⟧ Bᵣ) (TS (ST x) {B} b) (x b) -- (mapF (map-⊎ id id) x)
  STS' x {B} Bᵣ {b} bᵣ = let k = ⟦STS⟧ {x} {λ {B} b → {!!}} {!!} Bᵣ {b} {b} bᵣ in {!k!} -- {!mapFᵣ ? (Aᵣ ⟦⊎⟧ Bᵣ) (⟦map-⊎⟧ _ _ _ _ id ?)!}
  STS : ∀ (x : S) → (λ {B} → TS (ST x) {B}) ≡ x
  STS x = {!!}
  TST' : ∀ (t : T) → ⟦T⟧ (ST (TS t)) (mapF id t)
  TST' t = mapFᵣ (Aᵣ ⟦⊎⟧ ⟦𝟙⟧) _ (λ xᵣ → {!⟦map-⊎⟧ _ _ _ _ id ? xᵣ!}) (Fᵣ-refl {!!})
  -}

module TestIso = Iso {Maybe} ⟦Maybe⟧ (λ r {x} → ⟦Maybe⟧-Properties.refl (λ _ → r) x) {map?} ⟦map?⟧ {ℕ} _≡_ refl
