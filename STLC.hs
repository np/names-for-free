
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
UndecidableInstances, IncoherentInstances, OverloadedStrings,
DataKinds, TypeFamilies, PolyKinds #-}

module STLC where

data Type where 
     Boo :: Type
     Arr :: Type -> Type -> Type

type family EvT (t :: Type) :: * 
     
type instance EvT Boo = Bool     
type instance EvT (Arr t t') = EvT t -> EvT t'

data (∪) u v (τ :: Type) where
  Inl :: u τ -> (u ∪ v) τ
  Inr :: v τ -> (u ∪ v) τ

data (⊎) u v (τ :: Type') where
  Inl' :: u τ -> (u ⊎ v) τ
  Inr' :: v τ -> (u ⊎ v) τ


-- Terms, with additional Type index.
data Term v τ where 
     Tru :: Term v Boo
     Fals :: Term v Boo
     Var :: v τ -> Term v τ
     App :: Term v (Arr τ1 τ2) -> Term v τ1 -> Term v τ2
     Abs :: (forall w. w τ1 -> Term (v ∪ w) τ2) -> Term v (Arr τ1 τ2)

type v --> w = forall ty. forall (τ :: ty). v τ -> w τ

mapu :: (u --> u') -> (v --> v') -> (u ∪ v) --> (u' ∪ v')
mapu f g (Inl x) = Inl (f x)
mapu f g (Inr x) = Inr (g x)

fmap' :: v --> w -> Term v --> Term w
fmap' f Tru = Tru
fmap' f Fals = Fals
fmap' f (Var v) = Var (f v)
fmap' f (App t t₁) = App (fmap' f t) (fmap' f t₁)
fmap' f (Abs x) = Abs (\y → fmap' (mapu f id) (x y))

untag :: (v ∪ v) --> v
untag (Inl x) = x
untag (Inr y) = y

{-
eval :: Term EvT τ -> EvT τ
eval Tru = True
eval Fals = False
eval (Var v) = v
eval (App y y') = eval y (eval y')
eval (Abs {τ1} {τ2} y) = \ t -> eval (fmap (merge ⟦_⟧) (y t))
-}


data Type' :: * where
  Boo' :: Type'
  Not :: Type' -> Type'
  (:×) :: Type' -> Type' -> Type'

cpsType :: Type -> Type'
cpsType Boo = Boo'
cpsType (Arr τ1 τ2) = Not (cpsType τ1 :× (Not (cpsType τ2)))

data Primop (v :: Type' -> *) (ρ :: Type') (τ :: Type') :: * where 
  Tru' :: Primop v ρ Boo'
  Fals' :: Primop v ρ Boo'
  Var' :: v τ -> Primop v ρ τ
  Abs' :: (∀ w. w τ1 -> Term' (v ⊎ w) ρ) -> Primop v ρ (Not τ1)
  (:-) :: v τ1 -> v τ2 -> Primop v ρ (τ1 :× τ2)    
  Π1   :: v (τ1 :× τ2) -> Primop v ρ τ1
  Π2   :: v (τ1 :× τ2) -> Primop v ρ τ2


data Term' (v :: Type' -> *) (ρ :: Type') :: * where 
  Halt' :: v τ -> Term' v τ
  App'  :: v (Not τ1) -> v τ1 -> Term' v ρ
  Let   :: Primop v ρ τ1 -> (∀ w. w τ1 -> Term' (v ⊎ w) ρ) -> Term' v ρ


fmap'' :: (v --> w) -> Term' v --> Term' w 
fmap'' = undefined

untag' :: (v ⊎ v) --> v
untag' (Inl' x) = x
untag' (Inr' y) = y

mapu' :: (u --> u') -> (v --> v') -> (u ⊎ v) --> (u' ⊎ v')
mapu' f g (Inl' x) = Inl' (f x)
mapu' f g (Inr' x) = Inr' (g x)


spliceAbs :: ∀ v τ1 τ2 τ3.
             (forall w. w τ3 → Term' (v ⊎ w) τ1) -> 
             (∀ w. w τ1 → Term' (v ⊎ w) τ2) -> 
             forall w. w τ3 → Term' (v ⊎ w) τ2
spliceAbs e' e2 x = splice (e' x) (\ x₁ → fmap'' (mapu' Inl' id) (e2 x₁))

-- in e1, substitude Halt' by an arbitrary continuation e2
splice :: forall v τ1 τ2.
         Term' v τ1 ->
         (∀ w. w τ1 -> Term' (v ⊎ w) τ2) -> 
         Term' v τ2
splice (Halt' v) e2 =  fmap'' untag' (e2 v)
splice (App' f x) e2 = App' f x
splice (Let p e') e2 = Let (splicePrim p e2)  ( spliceAbs e' e2 )

splicePrim :: forall t v τ1 τ2. Primop v τ1 t ->  (∀ w. w τ1 -> Term' (v ⊎ w) τ2) -> Primop v τ2 t
splicePrim (Abs' e) e2 = Abs' (spliceAbs e e2)
splicePrim Tru' e2 = Tru'
splicePrim Fals' e2 = Fals'
splicePrim (Var' v) e2 = Var' v
splicePrim (y :- y') e2 = y :- y'
splicePrim (Π1 y) e2 = Π1 y
splicePrim (Π2 y) e2 = Π2 y

comp :: (Type' -> a) -> (Type -> Type') -> (Type -> a)
comp f g x = f (g x)


cps :: Term (v `comp` cpsType) τ -> Term' v (cpsType τ)
cps Fals = Let Fals' (Halt' . Inr')

{-

cps Tru = Let Tru' (Halt' ∘ inj₂)
  cps Fals = Let Fals' (Halt' ∘ inj₂) 
  cps (Var v) = Halt' v
  cps {V} (App e1 e2) = splice (cps e1) \{Wf} f -> 
                        splice (fmap' inj₁ (cps e2))     \ x →
                        Let (Abs' (Halt' ∘ inj₂)) \k →
                        Let (inj₁ (inj₂ x) :- (inj₂ k))    \p ->
                        App' (inj₁ (inj₁ (inj₁ (inj₂ f)))) (inj₂ p)
  cps (Abs e') =  Let (Abs' \p -> Let (Π1 (inj₂ p)) \x -> 
                                  Let (Π2 (inj₁ (inj₂ p))) \k ->
                                  splice (fmap' {''} (cps (e' x))) \r -> 
                                  App' (inj₁ (inj₂ k)) (inj₂ r))
                  (Halt' ∘ inj₂) 

-}