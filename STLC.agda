{-# OPTIONS --type-in-type 
  #-}

-- This is a translated from "Parametric Higher-Order Abstract Syntax
-- for Mechanized Semantics", Adam Chlipala.


module STLC where

  open import Data.Nat
  open import Data.Bool
  open import Data.Unit
  open import Data.Sum renaming (map to map-⊎)
  open import Function
  open import Data.List
  open import Data.Product hiding (_×_)


  data Type : Set where 
     Boo : Type
     Arr : Type -> Type -> Type

  ⟦_⟧ : Type -> Set 
  ⟦ Boo ⟧ = Bool
  ⟦ Arr τ τ' ⟧ = ⟦ τ ⟧ -> ⟦ τ' ⟧

  _∪_ : {Type : Set} (V W : Type -> Set) -> Type -> Set
  (V ∪ W) τ = V τ ⊎ W τ

  -- Terms, with additional Type index.
  data Term (V : Type -> Set) : (τ : Type) -> Set where 
     Tru : Term V Boo
     Fals : Term V Boo
     Var : {τ : Type} -> (v : V τ) -> Term V τ
     App : {τ1 τ2 : Type} -> Term V (Arr τ1 τ2) -> Term V τ1 -> Term V τ2
     Abs : {τ1 τ2 : Type} -> (∀ {W} -> W τ1 -> Term (V ∪ W) τ2) -> Term V (Arr τ1 τ2)

  _→̂_ : {Type : Set} (V W : Type -> Set) -> Set
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


  eval : forall {τ} -> Term ⟦_⟧ τ -> ⟦ τ ⟧
  eval Tru = true
  eval Fals = false
  eval (Var v) = v
  eval (App y y') = eval y (eval y')
  eval (Abs {τ1} {τ2} y) = \ t -> eval (fmap (merge ⟦_⟧) (y t))

  -- you've seen it coming: the CPS transform!
  data Type! : Set where
    Boo! : Type!
    Not : Type! -> Type!
    _×_ : Type! -> Type! -> Type!

  cpsType : Type -> Type!
  cpsType Boo = Boo!
  cpsType (Arr τ1 τ2) = Not (cpsType τ1 × (Not (cpsType τ2)))

  -- lots of details are hidden in the paper, and Coq syntax is really not helping.
  -- it would help to study CPS separately I guess ;)
  mutual
    data Primop (V : Type! -> Set) (ρ : Type!) : (τ : Type!) -> Set where 
      Tru! : Primop V ρ Boo!
      Fals! : Primop V ρ Boo!
      Var! : {τ : Type! } -> (v : V τ) -> Primop V ρ τ
      Abs! : {τ1 : Type! } -> (∀ {W} -> W τ1 -> Term! (V ∪ W) ρ) -> Primop V ρ (Not τ1)
      _,_ : {τ1 τ2 : Type! } -> V τ1 -> V τ2 -> Primop V ρ (τ1 × τ2)    
      π1 : {τ1 τ2 : Type! } -> V (τ1 × τ2) -> Primop V ρ τ1
      π2 : {τ1 τ2 : Type! } -> V (τ1 × τ2) -> Primop V ρ τ2
  

    data Term! (V : Type! -> Set) : (ρ : Type!) -> Set where 
      Halt! : {τ : Type! } -> (v : V τ) -> Term! V τ
      App!  : {ρ τ1 : Type! } -> V (Not τ1) -> V τ1 -> Term! V ρ
      Let   : {ρ τ1 : Type! } -> Primop V ρ τ1 -> (∀ {W} -> W τ1 -> Term! (V ∪ W) ρ) -> Term! V ρ


  fmap! : ∀ {V W} -> (V →̂ W) -> Term! V →̂ Term! W 
  fmap! = {!!}

  mutual 
    spliceAbs :  ∀ {V τ1 τ2 τ3} ->
                 ({W : Type! → Set} → W τ3 → Term! (λ τ → V τ ⊎ W τ) τ1) -> 
                 (∀ {W} -> W τ1 → Term! (V ∪ W) τ2) -> 
                 {W : Type! → Set} → W τ3 → Term! (λ τ → V τ ⊎ W τ) τ2
    spliceAbs {V} e' e2 {W} x = splice (e' x) (λ {U} x₁ → fmap! (map-⊎ inj₁ id) (e2 {U} x₁) )

    -- in e1, substitude Halt! by an arbitrary continuation e2
    splice : {V : Type! -> Set} {τ1 τ2 : Type! } 
             (e1 : Term! V τ1) 
             (e2 : ∀ {W} -> W τ1 -> Term! (V ∪ W) τ2) -> Term! V τ2
    splice {V} (Halt! v) e2 =  fmap! (merge V) (e2 v)
    splice (App! f x) e2 = App! f x
    splice (Let p e') e2 = Let (splicePrim p e2)  ( spliceAbs e' e2 )

    splicePrim : forall {t} {V : Type! -> Set} {τ1 τ2 : Type! } (p : Primop V τ1 t) (e2 : ∀ {W} -> W τ1 -> Term! (V ∪ W) τ2) -> Primop V τ2 t
    splicePrim (Abs! e) e2 = Abs! (spliceAbs e e2)
    splicePrim Tru! e2 = Tru!
    splicePrim Fals! e2 = Fals!
    splicePrim (Var! v) e2 = Var! v
    splicePrim (y , y') e2 = y , y'
    splicePrim (π1 y) e2 = π1 y
    splicePrim (π2 y) e2 = π2 y

  cps : {V : Type! -> Set} -> Term (V ∘ cpsType) →̂ (Term! V ∘ cpsType)
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


