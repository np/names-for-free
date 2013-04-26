{-# OPTIONS --type-in-type 
  #-}

-- This is a translated from "Parametric Higher-Order Abstract Syntax
-- for Mechanized Semantics", Adam Chlipala.


module STLC2 where

  open import Data.Nat
  open import Data.Bool
  open import Data.Unit
  open import Data.Sum renaming (map to map-⊎)
  open import Function
  open import Data.List
  open import Data.Product hiding (_×_)
  open import Type

  data Typ : Set where 
     Boo : Typ
     Arr : Typ -> Typ -> Typ

  ⟦_⟧ : Typ -> Set 
  ⟦ Boo ⟧ = Bool
  ⟦ Arr τ τ' ⟧ = ⟦ τ ⟧ -> ⟦ τ' ⟧

  _∪_ : {Typ : Set} (V W : Typ -> Set) -> Typ -> Set
  (V ∪ W) τ = V τ ⊎ W τ

  data Term (V : ★) : ★ where
    var : V → Term V
    abs : (∀ {W} → W → Term (V ⊎ W)) → Term V
    app : Term V → Term V → Term V
 
  mapTm : ∀{U V} → (U → V) → Term U → Term V
  mapTm f (abs t)   = abs (λ x → mapTm (map-⊎ f id) (t x))
  mapTm f (var x)   = var (f x)
  mapTm f (app t u) = app (mapTm f t) (mapTm f u)

  data _,_::_ {V W} (Γ : Typ -> V -> Set)  (x : W)  (τ : Typ) : Typ -> (V ⊎ W) -> Set where
    there : ∀ {x' τ'} -> Γ τ' x' → (Γ , x :: τ) τ' (inj₁ x')
    here : (Γ , x :: τ) τ (inj₂ x)

  -- Terms, with additional Typ index.
  data _⊢_::_ {V} (Γ : Typ -> V -> Set) : Term V -> (τ : Typ) -> Set where 
     -- Tru : Term V Boo
     -- Fals : Term V Boo
     Var : ∀ {x τ} -> Γ τ x -> Γ ⊢ var x :: τ 
     App : ∀ {t u τ1 τ2} -> Γ ⊢ t :: (Arr τ1 τ2) -> Γ  ⊢ u :: τ1 -> Γ ⊢ app t u :: τ2
     Abs : ∀ {τ1 τ2} {f : {W : Set} → W → Term (V ⊎ W)} -> (∀ {W} {Δ : Typ -> W -> Set} -> ∀ x -> Δ τ1 x -> 
                         (Γ , x :: τ1) ⊢ f x :: τ2) -> Γ ⊢ abs f :: (Arr τ1 τ2)
{-
  _→̂_ : {Typ : Set} (V W : Typ -> Set) -> Set
  V →̂ W = ∀ {τ} -> V τ -> W τ

  fmap : ∀ {V W} -> (V →̂ W) -> Term V →̂ Term W 
  fmap f Tru = Tru
  fmap f Fals = Fals
  fmap f (Var v) = Var (f v)
  fmap f (App t t₁) = App (fmap f t) (fmap f t₁)
  fmap f (Abs x) = Abs (λ x₁ → fmap (map-⊎ f id) (x x₁))

  merge : ∀ {T} -> (V : T -> Set) -> (V ∪ V) →̂ V
  merge _ (inj₁ x) = x
  merge _ (inj₂ y) = y

  ass : ∀ {T} -> (U V W : T -> Set) -> (U ∪ (V ∪ W)) →̂ ((U ∪ V) ∪ W)
  ass = {!!}

  wk : ∀ {T} -> (V W : T -> Set) -> V →̂ (V ∪ W)
  wk = {!!}

{-
  eval : forall {τ} -> Term ⟦_⟧ τ -> ⟦ τ ⟧
  eval Tru = true
  eval Fals = false
  eval (Var v) = v
  eval (App y y') = eval y (eval y')
  eval (Abs {τ1} {τ2} y) = \ t -> eval (fmap (merge ⟦_⟧) (y t))

  -- you've seen it coming: the CPS transform!
  data Typ! : Set where
    Boo! : Typ!
    Not : Typ! -> Typ!
    _×_ : Typ! -> Typ! -> Typ!

  cpsTyp : Typ -> Typ!
  cpsTyp Boo = Boo!
  cpsTyp (Arr τ1 τ2) = Not (cpsTyp τ1 × (Not (cpsTyp τ2)))

  -- lots of details are hidden in the paper, and Coq syntax is really not helping.
  -- it would help to study CPS separately I guess ;)
  mutual
    data Primop (V : Typ! -> Set) (ρ : Typ!) : (τ : Typ!) -> Set where 
      Tru! : Primop V ρ Boo!
      Fals! : Primop V ρ Boo!
      Var! : {τ : Typ! } -> (v : V τ) -> Primop V ρ τ
      Abs! : {τ1 : Typ! } -> (∀ {W} -> W τ1 -> Term! (V ∪ W) ρ) -> Primop V ρ (Not τ1)
      _,_ : {τ1 τ2 : Typ! } -> V τ1 -> V τ2 -> Primop V ρ (τ1 × τ2)    
      π1 : {τ1 τ2 : Typ! } -> V (τ1 × τ2) -> Primop V ρ τ1
      π2 : {τ1 τ2 : Typ! } -> V (τ1 × τ2) -> Primop V ρ τ2
  

    data Term! (V : Typ! -> Set) : (ρ : Typ!) -> Set where 
      Halt! : {τ : Typ! } -> (v : V τ) -> Term! V τ
      App!  : {ρ τ1 : Typ! } -> V (Not τ1) -> V τ1 -> Term! V ρ
      Let   : {ρ τ1 : Typ! } -> Primop V ρ τ1 -> (∀ {W} -> W τ1 -> Term! (V ∪ W) ρ) -> Term! V ρ


  fmap! : ∀ {V W} -> (V →̂ W) -> Term! V →̂ Term! W 
  fmap! = {!!}

  mutual 
    spliceAbs :  ∀ {V τ1 τ2 τ3} ->
                 ({W : Typ! → Set} → W τ3 → Term! (λ τ → V τ ⊎ W τ) τ1) -> 
                 (∀ {W} -> W τ1 → Term! (V ∪ W) τ2) -> 
                 {W : Typ! → Set} → W τ3 → Term! (λ τ → V τ ⊎ W τ) τ2
    spliceAbs {V} e' e2 {W} x = splice (e' x) (λ {U} x₁ → fmap! (map-⊎ inj₁ id) (e2 {U} x₁) )

    -- in e1, substitude Halt! by an arbitrary continuation e2
    splice : {V : Typ! -> Set} {τ1 τ2 : Typ! } 
             (e1 : Term! V τ1) 
             (e2 : ∀ {W} -> W τ1 -> Term! (V ∪ W) τ2) -> Term! V τ2
    splice {V} (Halt! v) e2 =  fmap! (merge V) (e2 v)
    splice (App! f x) e2 = App! f x
    splice (Let p e') e2 = Let (splicePrim p e2)  ( spliceAbs e' e2 )

    splicePrim : forall {t} {V : Typ! -> Set} {τ1 τ2 : Typ! } (p : Primop V τ1 t) (e2 : ∀ {W} -> W τ1 -> Term! (V ∪ W) τ2) -> Primop V τ2 t
    splicePrim (Abs! e) e2 = Abs! (spliceAbs e e2)
    splicePrim Tru! e2 = Tru!
    splicePrim Fals! e2 = Fals!
    splicePrim (Var! v) e2 = Var! v
    splicePrim (y , y') e2 = y , y'
    splicePrim (π1 y) e2 = π1 y
    splicePrim (π2 y) e2 = π2 y

  cps : {V : Typ! -> Set} -> Term (V ∘ cpsTyp) →̂ (Term! V ∘ cpsTyp)
  cps Tru = Let Tru! (Halt! ∘ inj₂)
  cps Fals = Let Fals! (Halt! ∘ inj₂) 
  cps (Var v) = Halt! v
  cps {V} (App e1 e2) = splice (cps e1) \{Wf} f -> 
                        splice (fmap! inj₁ (cps e2))     \ x →
                        Let (Abs! (Halt! ∘ inj₂)) \k →
                        Let (inj₁ (inj₂ x) , (inj₂ k))    \p ->
                        App! (inj₁ (inj₁ (inj₁ (inj₂ f)))) (inj₂ p)
  cps (Abs e') =  Let (Abs! \p -> Let (π1 (inj₂ p)) \x -> 
                                  Let (π2 (inj₁ (inj₂ p))) \k ->
                                  splice (fmap! {!!} (cps (e' x))) \r -> 
                                  App! (inj₁ (inj₂ k)) (inj₂ r))
                  (Halt! ∘ inj₂) 


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
