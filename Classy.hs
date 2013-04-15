{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings #-}
module Classy where

import Data.String
import Control.Monad (join)

--------------------------------
-- Generic programming prelude

data (∪) a b = Inl a | Inr b
data Zero
magic :: Zero -> a
magic _ = error "magic!"
instance Show Zero where show = magic

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

-------------------------------------------
-- Names as a simple wrapper around strings

newtype Name = Name { unName :: String }

-- Show them without quotes
instance Show Name where
  show = unName

instance IsString Name where
  fromString = Name . fromString

----------------------------------------
-- Term representation and examples

data Term v where
  Var :: v → Term v
  Lam :: Name → (forall w. w → Term (w ∪ v)) → Term v
  App :: Term v → Term v → Term v

var :: forall a b. (a :< b) => a → Term b
var = Var . inj

lam = Lam

id' :: Term Zero
id' = lam "x" (\x → var x)

const' :: Term Zero
const' = lam "x" (\x → lam "y" (\y → var x))


---------------------
-- Display code

instance Show x => Show (Term x) where
  show = disp

disp :: Show x => Term x → String
disp (Var x)    = show x
disp (App a b)  = "(" ++ disp a ++ ")" ++ disp b
disp (Lam nm f) = "λ" ++ unName nm ++ "." ++ disp (f nm)

---------------------
-- Catamorphism

cata :: All b a => ((a -> a) -> a, a -> a -> a) -> Term b -> a
cata (fl,fa) (Var x)   = prj x
cata (fl,fa) (App f a) = fa (cata (fl,fa) f) (cata (fl,fa) a)
cata (fl,fa) (Lam _ f) = fl (cata (fl,fa) . f)

class All a b where
  prj :: a -> b

instance All a a where
  prj = id

instance All b a => All (a ∪ b) a where
  prj (Inl a) = a
  prj (Inr a) = prj a

instance All Zero a where
  prj = magic

size :: Term Zero -> Int
size = cata (\f -> 1 + f 1, \a b -> 1 + a + b)

-----------------------------------------------------------
-- Terms are monads
-- (which means they support substitution as they should)


wk :: Term v → Term (w ∪ v)
wk = fmap Inr

-- Kleisli arrows arising from the Term monad
type v ⇶ w = v → Term w

-- Union is a functor in the category of Kleisli arrows (⇶)
lift :: v ⇶ w → (x ∪ v) ⇶ (x ∪ w)
lift θ (Inr x) = wk (θ x)
lift _ (Inl x) = Var (Inl x) -- also works: var x

instance Monad Term where
  Var x    >>= θ = θ x
  Lam nm t >>= θ = Lam nm (\x → t x >>= lift θ)
  App t u  >>= θ = App (t >>= θ) (u >>= θ)

  return = Var

subst :: v ⇶ w → Term v → Term w
subst = (=<<)

-- As with any monad, fmap can be derived from bind and return.
-- This is a bit nasty here though. Indeed the definition of bind
-- uses lift which uses wk which uses fmap.
instance Functor Term where
  fmap f t = t >>= return . f

-- Substitute in an open term
subst' :: (∀v. v → Term v) → Term w → Term w
subst' t u = join (t u)

-- Nbe
eval :: Term v -> Term v
eval (Var x) = Var x
eval (Lam n t) = Lam n (eval . t)
eval (App t u) = app (eval t) (eval u)

app :: Term v -> Term v -> Term v
app (Lam _ t) u = yak =<< t u
app t u = App t u

yak :: Term v ∪ v -> Term v
yak (Inl x) = x
yak (Inr x) = Var x



