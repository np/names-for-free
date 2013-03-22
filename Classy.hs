{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types, UnicodeSyntax, TypeOperators,
             GADTs, OverlappingInstances, UndecidableInstances, IncoherentInstances #-}
module Classy where
--------------------------------
-- Generic programming prelude

data (∪) a b = Inl a | Inr b
data Zero
instance Show Zero where show _ = error "magic!"

type a :+: b = a ∪ b

instance (Show a, Show b) => Show (a ∪ b) where
  show (Inl x) = show x
  show (Inr x) = show x

class a :< b where
  inj :: a → b

instance a :< (a ∪ b) where
  inj = Inl

instance (a :< c) => a :< (b ∪ c) where
  inj = Inr . inj

instance Functor ((∪) a) where
  fmap _ (Inl x) = Inl x
  fmap f (Inr x) = Inr (f x)

----------------------------------------
-- Term representation and examples

data Term v where
  Var :: v → Term v
  Lam :: String → (forall w. w → Term (w ∪ v)) → Term v
  App :: Term v → Term v → Term v

var :: forall a b. (a :< b) => a → Term b
var = Var . inj

lam = Lam

id' :: Term Zero
id' = lam "x" (\x → var x)

const' :: Term Zero
const' = lam "x" (\_ → lam "y" (\y → var y))


---------------------
-- Display code

instance Show x => Show (Term x) where
  show = disp

disp :: Show x => Term x → String
disp  (Var x) = show x
disp  (App a b) = "(" ++ disp a ++ ")" ++ disp b
disp  (Lam nm f) = "λ" ++ nm ++ "." ++ disp (f nm)



-----------------------------------------------------------
-- Terms are monads
-- (which means they support substitution as they should)


wk :: Term v → Term (w ∪ v)
wk = fmap Inr

type v ⇶ w = v → Term w

lift :: v ⇶ w → (x ∪ v) ⇶ (x ∪ w)
lift θ (Inr x) = wk (θ x)
lift _ (Inl x) = Var (Inl x)

instance Monad Term where
  Var x    >>= θ = θ x
  Lam nm t >>= θ = Lam nm (\x → t x >>= lift θ)
  App t u  >>= θ = App (t >>= θ) (u >>= θ)

  return = Var

subst :: v ⇶ w → Term v → Term w
subst = (=<<)

instance Functor Term where
  fmap f (Var x)    = Var (f x)
  fmap f (Lam nm t) = Lam nm (\x → fmap (fmap f) (t x))
  fmap f (App t u)  = App (fmap f t) (fmap f u)

