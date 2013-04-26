{-# OPTIONS --type-in-type #-}
module Iso where

open import Type
open import Function
open import Data.Sum.NP renaming (map to map-⊎; ⟦map⟧ to ⟦map-⊎⟧)
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧) -- ; ⟦⊤⟧ to ⟦𝟙⟧)
open import Relation.Unary.Logical hiding ([★]) renaming ([★₀] to [★]) -- ; ⟦⊤⟧ to ⟦𝟙⟧)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Maybe.NP
open import Data.Empty -- renaming (⊥ to 𝟘)
open import Data.Unit -- renaming (⊤ to 𝟙)
open import Data.Nat.Logical
open import Relation.Binary


module Reboot 
  (s : ∀ {W} -> W -> W)
  (sR : (∀⟨ Wᵣ ∶ ⟦★⟧ ⟩⟦→⟧  Wᵣ ⟦→⟧ Wᵣ) s s)
  (A : ★)  
    where

   u : ∀ (x : A) -> s x ≡ x
   u x =  sR {ℕ} (\_ y -> y ≡ x) {zero} refl 

data [Maybe] {A} Ap : Maybe A -> ★ where
  nothing : [Maybe] Ap nothing
  just : (Ap [→] [Maybe] Ap) just


module MaybeF2
  (s : ∀ {W} -> W -> Maybe W)
  (sR : (∀⟨ Wᵣ ∶ ⟦★⟧ ⟩⟦→⟧  Wᵣ ⟦→⟧ ⟦Maybe⟧ Wᵣ) s s)
  (A : ★)
    where

  S = ∀ {W} -> W -> Maybe W 
  ⟦S⟧ = ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Bᵣ ⟦→⟧ ⟦Maybe⟧ Bᵣ

  T = Maybe ⊤
  ⟦T⟧ = ⟦Maybe⟧ ⟦⊤⟧

  TS : T -> S
  TS (just tt) = just 
  TS nothing = λ x → nothing

  ST : S -> T
  ST s = s tt

  test : {!!}
  test = {!sR (\x -> !} 


module MaybeF 
  (s : ∀ {W} -> W -> Maybe W)
  (sR : (∀⟨ Wᵣ ∶ [★] ⟩[→]  Wᵣ [→] [Maybe] Wᵣ) s)
  (A : ★)
    where

  S = ∀ {W} -> W -> Maybe W 
  [S] = ∀⟨ Bᵣ ∶ [★] ⟩[→] Bᵣ [→] [Maybe] Bᵣ

  T = Maybe ⊤
  [T] = [Maybe] [⊤]

  TS : T -> S
  TS (just tt) = just 
  TS nothing = λ x → nothing

  ST : S -> T
  ST s = s tt

  u' : ∀ (x : A) -> [Maybe] (λ y → y ≡ x) (s x)
  u' x = sR (λ y → y ≡ x) refl


  u'' : ∀ (x : A) -> [Maybe] (λ y → y ≡ x) (s x)
  u'' x = sR (λ y → y ≡ x) refl


  lem : (x : A) -> [Maybe] (λ y → y ≡ x) (s x) -> s x ≡ just x ⊎ s x ≡ nothing
  lem  x t with s x
  lem x nothing | .nothing = inj₂ refl
  lem x (just {x₁} xₚ) | .(just x₁) = inj₁ (cong just xₚ) 

  lem' : s {A} ≡ just ⊎ s {A} ≡ const nothing
  lem' = {!!}


  final : (x : A) -> TS (ST s) x ≡ s x
  final with lem' 
  final | inj₁ x = {!!}
  final | inj₂ y = {!!} 

{-
module Easy
         {F : ★ → ★}
         (Fᵣ : ([★] [→] [★]) F)
--         (Fᵣ-refl : ∀ {A} {Aᵣ : Rel A _} → Reflexive Aᵣ → Reflexive (Fᵣ Aᵣ))
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ [★] ⟩[→] ∀⟨ Bᵣ ∶ [★] ⟩[→] (Aᵣ [→] Bᵣ) [→] Fᵣ Aᵣ [→] Fᵣ Bᵣ) mapF)
  (s : ∀ {W} -> W -> F W)
  (sR : (∀⟨ Wᵣ ∶ [★] ⟩[→]  Wᵣ [→] Fᵣ Wᵣ) s)
  (A : ★)  
  (Aᵣ : [★] A)
  -- (Aᵣ-refl : Reflexive Aᵣ) 
    where

   u : ∀ (x : A) -> Fᵣ (λ y → y ≡ x) (s x) 
   u x = sR (λ y → y ≡ x) refl
-}


{-
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
  Aᵣ+1 = Aᵣ ⟦⊎⟧ ⟦⊤⟧
  S = ∀ {B} → B → F (A ⊎ B)
  ⟦S⟧ = ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Bᵣ ⟦→⟧ Fᵣ (Aᵣ ⟦⊎⟧ Bᵣ)
  T = F (A ⊎ ⊤)
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
  
  ⟦S⟧-refl : Reflexive ⟦S⟧
  ⟦S⟧-refl {s} {B₁} {B₂} Bᵣ {b₁} {b₂} bᵣ = {!!}

  bla : ∀ (s : S) → Fᵣ Aᵣ+1 (TS (ST s) tt) (mapF (map-⊎ id (const tt)) (s tt))
  bla s = ⟦STS⟧ (⟦S⟧-refl {s}) ⟦⊤⟧ {tt} _
  bla' : ∀ (s : S) {B} (b : B) → Fᵣ (Aᵣ ⟦⊎⟧ {!!}) (TS (ST s) b) (mapF (map-⊎ id (const b)) (s b))
  bla' s {B} b = {!⟦STS⟧ (⟦S⟧-refl {s}) ? {b} _ !}
  STS' : ∀ (x : S) {B} (Bᵣ : ⟦★⟧ B B) {b} (bᵣ : Bᵣ b b) → Fᵣ (Aᵣ ⟦⊎⟧ Bᵣ) (TS (ST x) {B} b) (x b) -- (mapF (map-⊎ id id) x)
  STS' x {B} Bᵣ {b} bᵣ = let k = ⟦STS⟧ {x} {λ {B} b → {!!}} {!!} Bᵣ {b} {b} bᵣ in {!k!} -- {!mapFᵣ ? (Aᵣ ⟦⊎⟧ Bᵣ) (⟦map-⊎⟧ _ _ _ _ id ?)!}

  Full : ∀ {A B} -> A -> B -> Set
  Full _ _ = ⊤
 
 
  lemma : ∀ (s : S) {B} (b : B) ->  Fᵣ (Aᵣ ⟦⊎⟧ Full) (s b) (s tt)
  lemma s {B} b = ⟦S⟧-refl {s} {B} {⊤} Full {b} {_} tt

  STS'' : ∀ (s : S) {B} (b : B) -> Fᵣ (Aᵣ ⟦⊎⟧ Full) (mapF (map-⊎ id (const b)) (s tt)) (s b)
  STS'' s {B} b  = {! mapFᵣ _ _ (⟦map-⊎⟧ _ _ _ _ id (const ?)) (lemma s b)  !}


  {- STS : ∀ (x : S) → (λ {B} → TS (ST x) {B}) ≡ x
  STS x = {!!}
  TST' : ∀ (t : T) → ⟦T⟧ (ST (TS t)) (mapF id t)
  TST' t = mapFᵣ (Aᵣ ⟦⊎⟧ ⟦𝟙⟧) _ (λ xᵣ → {!⟦map-⊎⟧ _ _ _ _ id ? xᵣ!}) (Fᵣ-refl {!!})
  -- -}

module TestIso = Iso {Maybe} ⟦Maybe⟧ (λ r {x} → ⟦Maybe⟧-Properties.refl (λ _ → r) x) {map?} ⟦map?⟧ {ℕ} _≡_ refl
-- -}
-- -}
-- -}
