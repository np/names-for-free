{-# OPTIONS --type-in-type #-}
module Iso where

open import Type
open import Function.NP
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
    <_> : (f : A → B) → A → B → ★
    < f > x y = Bᵣ (f x) y

module F≡id
  (s  : ∀ {A} → A → A)
  (sᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Aᵣ ⟦→⟧ Aᵣ) s s)
  (A  : ★)  
  where

  s≗id : ∀ (x : A) → s x ≡ x
  s≗id x = sᵣ {𝟙} (\_ y → y ≡ x) refl 

module F≡Maybe where

  S = ∀ {W} → W → Maybe W 
  ⟦S⟧ = ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Bᵣ ⟦→⟧ ⟦Maybe⟧ Bᵣ

  T = Maybe 𝟙
  ⟦T⟧ = ⟦Maybe⟧ ⟦𝟙⟧

  TS : T → S
  TS t b = map? (const b) t

  ST : S → T
  ST s = s tt

  module _
    (s  : ∀ {A} → A → Maybe A)
    (sᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧  Aᵣ ⟦→⟧ ⟦Maybe⟧ Aᵣ) s s)
    (A  : ★)
    (b : A)
    where
    lem : ⟦Maybe⟧ {!!} (TS (s tt) b) (s b)
    lem = {!!}

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
  TS t b = map? (const b) t

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

⟦⟧-trans : ∀ {A : ★} (Aᵣ : ⟦★⟧ A A) {B : ★} (Bᵣ : ⟦★⟧ B B)
           → Reflexive Aᵣ → Transitive Bᵣ → Transitive (Aᵣ ⟦→⟧ Bᵣ)
⟦⟧-trans Aᵣ Bᵣ Aᵣ-refl Bᵣ-trans p q xᵣ = Bᵣ-trans (p xᵣ) (q Aᵣ-refl)
-- ⟦⟧-trans Aᵣ Bᵣ Aᵣ-refl Bᵣ-trans p q xᵣ = Bᵣ-trans (p Aᵣ-refl) (q xᵣ)

ID = ∀ {A : ★} → A → A
[ID] = ∀⟨ Aₚ ∶ [★] ⟩[→] Aₚ [→] Aₚ

{-
module Subst
         (prop : ★ → ★)
         (_$_ : ∀ {A} → prop A → A → ★)
         {A}
         {x y : A}
         (P : prop A)
         (Px : P $ x)
         where
  Py : P $ y
  Py = {!!}

module Client
         (prop : ★ → ★)
         (_$_ : ∀ {A} → prop A → A → ★)
         (p★ : prop ★)
         (_p→_ : prop ★ → prop ★ → prop ★)
         (pℕ : p★ $ ℕ)
         (pzero : pℕ $ zero)
         (psuc : (pℕ p→ pℕ) suc)
         (subst : ∀ {A} {x y : A} (P : prop A) (Px : P $ x) → P $ y) where
  Py = {!!}
  -}

{-
Q x y P = P x → P y
sbst : ∀ {A : ★} {x y : A} (P : A → ★) →
         let Aᵣ : ⟦★⟧ A A
             Aᵣ = {!!}
         in Aᵣ x y → P x → P y
sbst = {!!}
-}

-- could be generalized to f g : A -> B
SubstLeft : ∀ {A : ★} (Aᵣ : ⟦★⟧ A A) → ★
SubstLeft {A} Aᵣ = 
                 ∀ (f : A → A)
                   (g : A → A)
                 → (Aᵣ ⟦→⟧ Aᵣ) f g
                 → ∀ {x₁ x₂}
                 → Aᵣ x₁ (f x₂)
                 → Aᵣ x₁ (g x₂)

SubstLeftId : ∀ {A : ★} (Aᵣ : ⟦★⟧ A A) → ★
SubstLeftId {A} Aᵣ = 
                 ∀ (f : A → A)
                 → (Aᵣ ⟦→⟧ Aᵣ) f id
                 → ∀ {x₁ x₂}
                 → Aᵣ x₁ (f x₂)
                 → Aᵣ x₁ x₂

substLeftId : ∀ {A : ★} → SubstLeftId {A} _≡_
substLeftId {A} f f-id refl = f-id refl

-- substitute 
-- f = g
-- x1 = f x2
-- x1 = g x2
subst-left' : ∀ {A} (Aᵣ : ⟦★⟧ A A) → SubstLeft Aᵣ
subst-left' Aᵣ f g f-g xᵣ = {!f-g xᵣ!}
  where fᵣ : (Aᵣ ⟦→⟧ Aᵣ) f f
        fᵣ = {!!}

module Nat
         {F  : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         (mapF  : ∀ {A B} → (A → B) → F A → F B)
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         (mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id)
         {- unused
         (mapF-∘ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Cᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ((Bᵣ ⟦→⟧ Cᵣ) ⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ (Fᵣ Aᵣ ⟦→⟧ Fᵣ Cᵣ)))
                   (λ f g → mapF (f ∘ g)) (λ f g → mapF f ∘ mapF g))
         -}
         (α  : ∀ {X} → X → F X)
         (αᵣ : (∀⟨ Xᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Xᵣ) α α)
         (X  : ★)
         (Xᵣ : ⟦★⟧ X X)
         (Xᵣ-refl : Reflexive Xᵣ)
         (Y  : ★)
         (Yᵣ : ⟦★⟧ Y Y)
         (FᵣYᵣ-trans : Transitive (Fᵣ Yᵣ))
         (f  : X → Y)
         (fᵣ : (Xᵣ ⟦→⟧ Yᵣ) f f)
         (subst-leftIdFY : SubstLeftId (Fᵣ Yᵣ))
         where

  open RelOf {X} {Y} Yᵣ

  X→FYᵣ = Xᵣ ⟦→⟧ Fᵣ Yᵣ

  X→FYᵣ-trans : Transitive X→FYᵣ
  X→FYᵣ-trans = ⟦⟧-trans Xᵣ (Fᵣ Yᵣ) Xᵣ-refl FᵣYᵣ-trans

  C : (F Y → F Y) → X → F Y
  C g = g ∘ α ∘ f

  ⟦C⟧ : ((Fᵣ Yᵣ ⟦→⟧ Fᵣ Yᵣ) ⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Yᵣ) C C
  ⟦C⟧ gᵣ xᵣ = gᵣ (αᵣ Yᵣ (fᵣ xᵣ))

  nat' : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (mapF f ∘ α) (mapF id ∘ α ∘ f)
  nat' xᵣ = mapFᵣ < f > Yᵣ id (αᵣ < f > (fᵣ xᵣ))

  nat : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (mapF f ∘ α) (α ∘ f)
  nat xᵣ = X→FYᵣ-trans nat' (⟦C⟧ (mapF-id Yᵣ)) xᵣ

  nat'' : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (mapF f ∘ α) (α ∘ f)
  nat'' xᵣ = subst-leftIdFY (mapF id) (mapF-id Yᵣ) (nat' xᵣ)

module NatMaybe where
  F : ★ → ★
  F = Maybe
  Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F
  Fᵣ = ⟦Maybe⟧
  mapF : ∀ {A B} → (A → B) → F A → F B
  mapF = map?
  mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF
  mapFᵣ = ⟦map?⟧
  mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id
  mapF-id = ⟦map?-id⟧
  module α≡just where
    α : ∀ {X} → X → F X
    α = just
    αᵣ : (∀⟨ Xᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Xᵣ) α α
    αᵣ _ = just
  module α≡nothing where
    α : ∀ {X} → X → F X
    α _ = nothing
    αᵣ : (∀⟨ Xᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Xᵣ) α α
    αᵣ _ _ = nothing
  module X≡ℕ where
    X : ★
    X = ℕ
    Xᵣ : ⟦★⟧ X X
    Xᵣ = ⟦ℕ⟧
    Xᵣ-refl : Reflexive Xᵣ
    Xᵣ-refl = ⟦ℕ⟧ᵉ.refl
  module Y≡ℕ where
    Y  : ★
    Y = ℕ
    Yᵣ : ⟦★⟧ Y Y
    Yᵣ = ⟦ℕ⟧
    FᵣYᵣ-trans : Transitive (Fᵣ Yᵣ)
    FᵣYᵣ-trans = ⟦Maybe⟧-Properties.trans ⟦ℕ⟧ᵉ.trans
    subst-leftFY : SubstLeft (Fᵣ Yᵣ)
    subst-leftFY f g fg x = FᵣYᵣ-trans x (fg (⟦Maybe⟧-Properties.refl (λ _ → ⟦ℕ⟧ᵉ.refl) _))
    subst-leftIdFY : SubstLeftId (Fᵣ Yᵣ)
    -- subst-leftFYId f fid x = FᵣYᵣ-trans x (fid (⟦Maybe⟧-Properties.refl (λ _ → ⟦ℕ⟧ᵉ.refl) _))
    subst-leftIdFY f fid x = {!fid' x (⟦Maybe⟧ ⟦ℕ⟧ _)!}
      where fid' : ∀ {x₁ x₂} (xᵣ : ⟦Maybe⟧ ⟦ℕ⟧ x₁ x₂) (P : Maybe ℕ → ★) → P x₁ → P x₂
            fid' {x₁} {x₂} xᵣ P Px = {!!}
    {-
    subst-leftFYId f fid {just x} {just x₁} x₂ = FᵣYᵣ-trans x₂ (fid (just ⟦ℕ⟧ᵉ.refl))
    subst-leftFYId f fid {just x} {nothing} x₁ = FᵣYᵣ-trans x₁ (fid nothing)
    subst-leftFYId f fid {nothing} {just x} x₁ = {!!}
    subst-leftFYId f fid {nothing} {nothing} x = {!!}
    -}
  module f≡suc where
    open X≡ℕ public
    open Y≡ℕ public
    f : X → Y
    f = suc
    fᵣ : (Xᵣ ⟦→⟧ Yᵣ) f f
    fᵣ = suc

  module t1 where
    open α≡just
    open f≡suc
    nat : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (mapF f ∘ α) (α ∘ f)
    nat = Nat.nat Fᵣ mapF mapFᵣ mapF-id α αᵣ X Xᵣ Xᵣ-refl Y Yᵣ FᵣYᵣ-trans f fᵣ subst-leftIdFY

module _
         {F : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         (Fᵣ-refl : ∀ {A} {Aᵣ : Rel A _} → Reflexive Aᵣ → Reflexive (Fᵣ Aᵣ))
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         (mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id)
    where
    {-
    {A B C : ★} (f : B → C) (g : A → B)
    (Aᵣ : ⟦★⟧ A A)
    (Bᵣ : ⟦★⟧ B B)
    (Cᵣ : ⟦★⟧ C C)
    where
    FAFC = F A → F C
    ⟦FAFC⟧ = Fᵣ Aᵣ ⟦→⟧ Fᵣ Cᵣ
    f1 f2 : F A → F C
    f1 = mapF (f ∘ g)
    f2 = mapF f ∘ mapF g
    prop : ⟦FAFC⟧ f1 f2
    prop = {!!}
-}
module Iso
         {F : ★ → ★}
         (Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F)
         -- (Fᵣ-refl : ∀ {A} {Aᵣ : Rel A _} → Reflexive Aᵣ → Reflexive (Fᵣ Aᵣ))
         {mapF  : ∀ {A B} → (A → B) → F A → F B}
         (mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF)
         (mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id)
         {- unused
         (mapF-∘ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Cᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ((Bᵣ ⟦→⟧ Cᵣ) ⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ (Fᵣ Aᵣ ⟦→⟧ Fᵣ Cᵣ)))
                   (λ f g → mapF (f ∘ g)) (λ f g → mapF f ∘ mapF g))
         -}
         where
  S = ∀ {B} → B → F B
  ⟦S⟧ = ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Bᵣ ⟦→⟧ Fᵣ Bᵣ
  T = F 𝟙
  ⟦T⟧ = Fᵣ ⟦𝟙⟧
  -- ⟦T⟧-refl : Reflexive ⟦T⟧
  -- ⟦T⟧-refl = Fᵣ-refl _
  ST : S → T
  ST s = s tt
  ⟦ST⟧ : (⟦S⟧ ⟦→⟧ ⟦T⟧) ST ST
  ⟦ST⟧ sᵣ = sᵣ _ ⟦tt⟧
  TS : T → S
  TS t b = mapF (const b) t
  ⟦TS⟧ : (⟦T⟧ ⟦→⟧ ⟦S⟧) TS TS
  ⟦TS⟧ tᵣ Bᵣ bᵣ = mapFᵣ _ _ (const bᵣ) tᵣ

 -- nat : (Xᵣ ⟦→⟧ Fᵣ Yᵣ) (mapF f ∘ α) (α ∘ f)
  module _
         (α  : ∀ {X} → X → F X)
         (αᵣ : (∀⟨ Xᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Xᵣ ⟦→⟧ Fᵣ Xᵣ) α α)
         (Y  : ★)
         (Yᵣ : ⟦★⟧ Y Y)
         (y  : Y)
         (yᵣ : Yᵣ y y)
         (FᵣYᵣ-trans : Transitive (Fᵣ Yᵣ))
         (subst-leftIdFY : SubstLeftId (Fᵣ Yᵣ))
         where
    nat-direct : Fᵣ Yᵣ (mapF (const y) (α tt)) (mapF id (α y))
    nat-direct = mapFᵣ (λ _ → Yᵣ y) Yᵣ id (αᵣ _ yᵣ)

    open RelOf {𝟙} {Y} Yᵣ
    f : 𝟙 → Y
    f = const y
    fᵣ : (⟦𝟙⟧ ⟦→⟧ Yᵣ) f f
    fᵣ _ = yᵣ
    nat : Fᵣ Yᵣ (mapF f (α tt)) (α y)
    nat = Nat.nat Fᵣ mapF mapFᵣ mapF-id α αᵣ 𝟙 ⟦𝟙⟧ _ Y Yᵣ FᵣYᵣ-trans f fᵣ subst-leftIdFY ⟦tt⟧

  TST = ST ∘ TS
  ⟦TST⟧ = λ {t₁ t₂} (tᵣ : ⟦T⟧ t₁ t₂) → ⟦ST⟧ (⟦TS⟧ tᵣ)
  -- mapF id ≡ id
  TST' : ∀ {t : F 𝟙} (tᵣ : Fᵣ ⟦𝟙⟧ t t) → Fᵣ ⟦𝟙⟧ (ST (TS t)) (mapF id t)
  -- TST' = ⟦TST⟧ ⟦T⟧-refl
  TST' = ⟦TST⟧

  STS : S → S
  STS = TS ∘ ST
  ⟦STS⟧ = λ {t₁ t₂ : S} (tᵣ : ⟦S⟧ t₁ t₂) → (λ {x} {y} → ⟦TS⟧ (⟦ST⟧ tᵣ) {x} {y})
  
  const𝟙 : ∀ {A} → A → 𝟙 → A
  const𝟙 x _ = x

  {-
  STS-id : (⟦S⟧ ⟦→⟧ ⟦S⟧) STS id
  STS-id {α₁} {α₂} αᵣ {X₁} {X₂} Xᵣ {x₁} {x₂} xᵣ = {!nat' α₁ αᵣ!}
  -}

  SSR : (S → S) → (S → S) → ★
  SSR f₁ f₂ = ∀ (α : S) (αᵣ : ⟦S⟧ α α) X (Xᵣ : ⟦★⟧ X X) x (xᵣ : Xᵣ x x) → Fᵣ Xᵣ (f₁ α x) (f₂ α x)

  foo : (⟦S⟧ ⟦→⟧ ⟦S⟧) ⇒ SSR
  foo f _ αᵣ _ Xᵣ _ = f αᵣ Xᵣ

  STS-id' : SSR STS id
  STS-id' α αᵣ X Xᵣ x xᵣ = nat α αᵣ X Xᵣ x xᵣ {!!} {!!}

  {-
  module _ (α : ∀ {X} → X → F X) {X Y : ★} (f : X → Y) (x : X) where
    nat : mapF f (α x) ≡ α (f x)
    nat = {!!}

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


  {-
  ⟦S⟧-refl : Reflexive ⟦S⟧
  ⟦S⟧-refl {s} {B₁} {B₂} Bᵣ {b₁} {b₂} bᵣ = {!!}
  -}
  -}

module IsoMaybe where
  F : ★ → ★
  F = Maybe
  Fᵣ : (⟦★⟧ ⟦→⟧ ⟦★⟧) F F
  Fᵣ = ⟦Maybe⟧
  mapF : ∀ {A B} → (A → B) → F A → F B
  mapF = map?
  mapFᵣ : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ ∀⟨ Bᵣ ∶ ⟦★⟧ ⟩⟦→⟧ (Aᵣ ⟦→⟧ Bᵣ) ⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Bᵣ) mapF mapF
  mapFᵣ = ⟦map?⟧
  mapF-id : (∀⟨ Aᵣ ∶ ⟦★⟧ ⟩⟦→⟧ Fᵣ Aᵣ ⟦→⟧ Fᵣ Aᵣ) (mapF id) id
  mapF-id = ⟦map?-id⟧
  module M = Iso {F} Fᵣ {-?-} {mapF} mapFᵣ mapF-id

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
