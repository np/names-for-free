{-# OPTIONS --type-in-type #-}
module Iso where

open import Type
open import Function
open import Data.Sum.NP renaming (map to map-⊎; ⟦map⟧ to ⟦map-⊎⟧)
open import Relation.Binary.Logical hiding (⟦★⟧) renaming (⟦★₀⟧ to ⟦★⟧ ; ⟦⊤⟧ to ⟦𝟙⟧)
open import Relation.Unary.Logical hiding ([★]) renaming ([★₀] to [★] ; [⊤] to [𝟙])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Maybe.NP
open import Data.Empty -- renaming (⊥ to 𝟘)
open import Data.Unit renaming (⊤ to 𝟙)
open import Data.Nat.Logical
open import Relation.Binary
open import Relation.Binary.Simple using (Const)

-- Always : ∀ {a b c} {A : Set a} {B : Set b} → REL A B c
Always : ∀ {A : ★} {B : ★} → REL A B _
Always = Const 𝟙

{-

α(X) : X → F X

        α(X)
   X ---------→ F X
   ↑            ↑
  R|            |F R
   ↓            ↓
   Y ---------→ F Y
        α(Y)

        α(X)
   X ---------→ F X
   |            |
  f|            |F f
   ↓            ↓
   Y ---------→ F Y
        α(Y)

K x y = x

Given X:★, x:X

         α(𝟙)
    𝟙 ---------→ F 𝟙
    |            |
 K x|            |F(K x)
    ↓            ↓
    X ---------→ F X
         α(X)
-}

module RelOf {A B : ★} (Bᵣ : ⟦★⟧ B B) where
    ⟨_⟩ : (f : A → B) → A → B → ★
    ⟨ f ⟩ x y = Bᵣ (f x) y

module F≡id
  (s  : ∀ {A} → A → A)
  (sᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Aᵣ) s s)
  (A  : ★)  
  where

  s≗id : ∀ (x : A) → s x ≡ x
  s≗id x = sᵣ {𝟙} (\_ y → y ≡ x) refl 

module F≡Maybe
  (s  : ∀ {A} → A → Maybe A)
  (sᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧  Aᵣ ⟦→⟧ ⟦Maybe⟧ Aᵣ) s s)
  (A  : ★)
  where

  S = ∀ {W} → W → Maybe W 
  ⟦S⟧ = ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Bᵣ ⟦→⟧ ⟦Maybe⟧ Bᵣ

  T = Maybe 𝟙
  ⟦T⟧ = ⟦Maybe⟧ ⟦𝟙⟧

  TS : T → S
  TS (just tt) = just 
  TS nothing = λ x → nothing

  ST : S → T
  ST s = s tt

  test : {!!}
  test = {!sR (\x → !} 


module MaybeF 
  (s : ∀ {W} → W → Maybe W)
  (sR : (∀⟨ Aᵣ ∶ [★] ⟩[→]  Aᵣ [→] [Maybe] Aᵣ) s)
  (A : ★)
    where

  S = ∀ {W} → W → Maybe W 
  [S] = ∀⟨ Bᵣ ∶ [★] ⟩[→] Bᵣ [→] [Maybe] Bᵣ

  T = Maybe 𝟙
  [T] = [Maybe] [𝟙]

  TS : T → S
  TS (just tt) = just 
  TS nothing = λ x → nothing

  ST : S → T
  ST s = s tt

  u' : ∀ (x : A) → [Maybe] (λ y → y ≡ x) (s x)
  u' x = sR (λ y → y ≡ x) refl


  u'' : ∀ (x : A) → [Maybe] (λ y → y ≡ x) (s x)
  u'' x = sR (λ y → y ≡ x) refl


  lem : (x : A) → [Maybe] (λ y → y ≡ x) (s x) → s x ≡ just x ⊎ s x ≡ nothing
  lem  x t with s x
  lem x nothing | .nothing = inj₂ refl
  lem x (just {x₁} xₚ) | .(just x₁) = inj₁ (cong just xₚ) 

  lem' : s {A} ≡ just ⊎ s {A} ≡ const nothing
  lem' = {!!}


  final : (x : A) → TS (ST s) x ≡ s x
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
  (s : ∀ {W} → W → F W)
  (sR : (∀⟨ Aᵣ ∶ [★] ⟩[→]  Aᵣ [→] Fᵣ Aᵣ) s)
  (A : ★)  
  (Aᵣ : [★] A)
  -- (Aᵣ-refl : Reflexive Aᵣ) 
    where

   u : ∀ (x : A) → Fᵣ (λ y → y ≡ x) (s x) 
   u x = sR (λ y → y ≡ x) refl
-}

module Nat
         {F  : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         (mapF  : ∀ {A B} → (A → B) → F A → F B)
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         (mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id)
         -- (mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) id (mapF id))
         -- (mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) f (mapF id))

         -- f = map id ∘ g → f = g
         -- (mapF-id : ∀ {A₁ A₂} (Aᵣ : ⟦★⟧ A₁ A₂) {B₁ B₂} (Bᵣ : ⟦★⟧ B₁ B₂) f g → (Aᵣ ⟦→⟧ Fᵣ Bᵣ) f (mapF id ∘ g) → (Aᵣ ⟦→⟧ Fᵣ Bᵣ) f g)

         -- f = h ∘ g → h = id → f = g
         -- (mapF-id' : ∀ {A₁ A₂} (Aᵣ : ⟦★⟧ A₁ A₂) {B₁ B₂} (Bᵣ : ⟦★⟧ B₁ B₂) f g → (Aᵣ ⟦→⟧ Fᵣ Bᵣ) f ( ∘ g) → (Aᵣ ⟦→⟧ Fᵣ Bᵣ) f g)

         -- f = id ∘ g → f = g
         (α  : ∀ {X} → X → F X)
         (αᵣ : (∀⟨ Xᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Xᵣ) α α)
         (X  : ★)
         (Xᵣ : ⟦★⟧ X X)
         (Y  : ★)
         (Yᵣ : ⟦★⟧ Y Y)
         (f  : X → Y)
         (fᵣ : (Xᵣ ⟦→⟧ Yᵣ) f f)
         where
  open RelOf {X} {Y} Yᵣ
  
  {-
  C : (F Y → F Y) → X → F Y
  C g = g ∘ α ∘ f
  foo : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (C (mapF id)) (C id)
  foo = {!!}
  -}
  nat' : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (mapF f ∘ α) (mapF id ∘ α ∘ f)
  nat' {x₁} {x₂} xᵣ = mapFᵣ (⟨ f ⟩) Yᵣ {f} {id} id {α x₁} {α (f x₂)} (αᵣ (⟨ f ⟩) {x₁} {f x₂} (fᵣ xᵣ))
  {-
  nat : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (mapF f ∘ α) (α ∘ f)
  -- nat {x₁} {x₂} xᵣ = mapF-id Xᵣ Yᵣ (mapF f ∘ α) (α ∘ f) nat' {x₁} {x₂} xᵣ
  nat {x₁} {x₂} xᵣ = {!foo!}
  -}


module Iso
         {F : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         (Fᵣ-refl : ∀ {A} {Aᵣ : Rel A _} → Reflexive Aᵣ → Reflexive (Fᵣ Aᵣ))
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         --(mapF-id : ∀ {A₁ A₂} (Aᵣ : ⟦★⟧ A₁ A₂) → (Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) id (mapF id))
         --(mapF-id : ∀ {A₁ A₂} (Aᵣ : ⟦★⟧ A₁ A₂) → (Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id)
         where
  S = ∀ {B} → B → F B
  ⟦S⟧ = ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Bᵣ ⟦→⟧ Fᵣ Bᵣ
  T = F 𝟙
  ⟦T⟧ = Fᵣ ⟦𝟙⟧
  ⟦T⟧-refl : Reflexive ⟦T⟧
  ⟦T⟧-refl = Fᵣ-refl _
  ST : S → T
  ST s = s tt
  ⟦ST⟧ : (⟦S⟧ ⟦→⟧ ⟦T⟧) ST ST
  ⟦ST⟧ sᵣ = sᵣ _ ⟦tt⟧
  TS : T → S
  TS t b = mapF (const b) t
  ⟦TS⟧ : (⟦T⟧ ⟦→⟧ ⟦S⟧) TS TS
  ⟦TS⟧ tᵣ Bᵣ bᵣ = mapFᵣ _ _ (const bᵣ) tᵣ

  TST = ST ∘ TS
  ⟦TST⟧ = λ {t₁ t₂} (tᵣ : ⟦T⟧ t₁ t₂) → ⟦ST⟧ (⟦TS⟧ tᵣ)
  -- mapF id ≡ id
  TST' : ∀ {t : F 𝟙} → Fᵣ ⟦𝟙⟧ (ST (TS t)) (mapF id t)
  TST' = ⟦TST⟧ ⟦T⟧-refl

  STS = TS ∘ ST
  ⟦STS⟧ = λ {t₁ t₂ : S} (tᵣ : ⟦S⟧ t₁ t₂) → (λ {x} {y} → ⟦TS⟧ (⟦ST⟧ tᵣ) {x} {y})
  
  const𝟙 : ∀ {A} → A → 𝟙 → A
  const𝟙 x _ = x

  -- Fᵣ (λ _ _ → 𝟙) ⇔ λ _ _ → 𝟙
{-

α(X) : X → F X

        α(X)
   X ---------→ F X
   ↑            ↑
  R|            |F R
   ↓            ↓
   Y ---------→ F Y
        α(Y)
-}

  {-
  module _ (α : ∀ {X} → X → F X) {X Y : ★} (R : X → Y → ★) (x : X) where
    nat : mapF R (α x) ≡ α (R x)
    nat = {!!}
  -}

  module _ (α : ∀ {X} → X → F X) {X Y : ★} (f : X → Y) (x : X) where
    nat : mapF f (α x) ≡ α (f x)
    nat = {!!}

    {-
    Fᵣ' = λ FYᵣ → RelOf.⟨_⟩ FYᵣ (mapF f)
    Fᵣ→Fᵣ' : ∀ {Xᵣ} {x y} → Fᵣ Xᵣ x y → Fᵣ' Xᵣ x y
    Fᵣ→Fᵣ' = ?

    open RelOf {X} {Y} _≡_
    nat'' : Fᵣ _≡_ (mapF f (α x)) (mapF id (α (f x)))
    nat'' = mapFᵣ (⟨ f ⟩) _≡_ {f} {id} sym {α x} {α (f x)} {!!}

    nat' : Fᵣ _≡_ (mapF f (α x)) (α (f x))
    nat' = {!mapFᵣ ? _≡_ {f} {id} ? {α x} {α (f x)} ?!}

  module _ (α : ∀ {X} → X → F X) {Y : ★} (y : Y) where
    scratch : mapF (λ _ → y) (α tt) ≡ α y
    scratch = nat α {𝟙} {Y} (λ _ → y) tt
    scratch' : Fᵣ _ (mapF (λ _ → y) (α tt)) (α y)
    scratch' = nat' α {𝟙} {Y} (λ _ → y) tt

  bla' : ∀ (s : S) (X : ★) (Xᵣ : ⟦★⟧ X X) (x : X) → Fᵣ Xᵣ (mapF (const𝟙 x) (s tt)) (s x)
  bla' s X Xᵣ x = let k = mapFᵣ {𝟙} {X} (λ _ _ → 𝟙) Xᵣ {const𝟙 x} {id} {!!} {s tt} {s x} {!!} in {!scratch' s {X} x!}
    where open RelOf {{!!}} {{!!}} {!!}

  bla : ∀ (s : S) (X : ★) (Xᵣ : ⟦★⟧ X X) (x : X) → Fᵣ Xᵣ (TS (ST s) x) (s x)
  bla s X Xᵣ x = bla' s X Xᵣ x

  {-
  ⟦S⟧-refl : Reflexive ⟦S⟧
  ⟦S⟧-refl {s} {B₁} {B₂} Bᵣ {b₁} {b₂} bᵣ = {!!}
  -}

  {-
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
  
  ⟦S⟧-refl : Reflexive ⟦S⟧
  ⟦S⟧-refl {s} {B₁} {B₂} Bᵣ {b₁} {b₂} bᵣ = {!!}

  bla : ∀ (s : S) → Fᵣ Aᵣ+1 (TS (ST s) tt) (mapF (map-⊎ id (const tt)) (s tt))
  bla s = ⟦STS⟧ (⟦S⟧-refl {s}) ⟦𝟙⟧ {tt} _
  bla' : ∀ (s : S) {B} (b : B) → Fᵣ (Aᵣ ⟦⊎⟧ {!!}) (TS (ST s) b) (mapF (map-⊎ id (const b)) (s b))
  bla' s {B} b = {!⟦STS⟧ (⟦S⟧-refl {s}) ? {b} _ !}
  STS' : ∀ (x : S) {B} (Bᵣ : ⟦★⟧ B B) {b} (bᵣ : Bᵣ b b) → Fᵣ (Aᵣ ⟦⊎⟧ Bᵣ) (TS (ST x) {B} b) (x b) -- (mapF (map-⊎ id id) x)
  STS' x {B} Bᵣ {b} bᵣ = let k = ⟦STS⟧ {x} {λ {B} b → {!!}} {!!} Bᵣ {b} {b} bᵣ in {!k!} -- {!mapFᵣ ? (Aᵣ ⟦⊎⟧ Bᵣ) (⟦map-⊎⟧ _ _ _ _ id ?)!}
 
 
  lemma : ∀ (s : S) {B} (b : B) →  Fᵣ (Aᵣ ⟦⊎⟧ Always) (s b) (s tt)
  lemma s {B} b = ⟦S⟧-refl {s} {B} {𝟙} Always {b} {_} tt

  STS'' : ∀ (s : S) {B} (b : B) → Fᵣ (Aᵣ ⟦⊎⟧ Always) (mapF (map-⊎ id (const b)) (s tt)) (s b)
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
-- -}
-- -}
-- -}
-- -}
