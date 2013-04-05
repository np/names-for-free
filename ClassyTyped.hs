{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings #-}
module Classy where

import Data.String
import Control.Applicative (Const(..))

data Hole = Hole
hole = undefined

--------------------------------
-- Generic programming prelude

class Show1 f where
  show1 :: f a -> String

instance Show a => Show1 (Const a) where
  show1 = show . getConst

data (∪) f g a = Inl (f a) | Inr (g a)
data Zero a
magic :: Zero a -> b
magic _ = error "magic!"
instance Show (Zero a) where show = magic
instance Show1 Zero where show1 = magic

type a :+: b = a ∪ b

instance (Show1 f, Show1 g) => Show1 (f ∪ g) where
  show1 (Inl x) = show1 x
  show1 (Inr x) = show1 x

type f →° g = forall a. f a → g a

class f :< g where
  inj :: f →° g

instance f :< (f ∪ g) where
  inj = Inl

instance (f :< h) => f :< (g ∪ h) where
  inj = Inr . inj

class IFunctor f where
  imap :: (g →° h) → f g →° f h

infixl 1 >>>=
infixr 1 =<<<
class IMonad f where
  ireturn :: a →° f a
  (=<<<)  :: (a →° f b) → f a →° f b
  (=<<<)  = flip (>>>=)
  (>>>=)  :: f a x → (a →° f b) → f b x
  (>>>=)  = flip (=<<<)

instance IFunctor ((∪) f) where
  imap _ (Inl x) = Inl x
  imap f (Inr x) = Inr (f x)

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

data Term v t where
  Var :: v t → Term v t
  Lam :: Name → (forall w. w s → Term (w ∪ v) t)
              → Term v (s → t)
  App :: Term v (s → t) → Term v s → Term v t

var :: (v :< w) => v t → Term w t
var = Var . inj

lam = Lam

id' :: Term Zero (a → a)
id' = lam "x" (\x → var x)

const' :: Term Zero (a → b → a)
const' = lam "x" (\x → lam "y" (\y → var x))

---------------------
-- Display code

instance Show1 v => Show1 (Term v) where
  show1 = disp

-- half broken since names are never freshen
disp :: Show1 v => Term v t → String
disp (Var x)    = show1 x
disp (App a b)  = "(" ++ disp a ++ ")" ++ disp b
disp (Lam nm f) = "λ" ++ unName nm ++ "." ++ disp (f (Const nm))

instance Show1 v => Show (Term v t) where
  show = show1


-----------------------------------------------------------
-- Terms are monads
-- (which means they support substitution as they should)


wk :: Term v →° Term (w ∪ v)
wk = imap Inr

type v ⇶ w = v →° Term w

lift :: v ⇶ w → (x ∪ v) ⇶ (x ∪ w)
lift θ (Inr x) = wk (θ x)
lift _ (Inl x) = Var (Inl x)

instance IMonad Term where
  Var x    >>>= θ = θ x
  Lam nm t >>>= θ = Lam nm (\x → t x >>>= lift θ)
  App t u  >>>= θ = App (t >>>= θ) (u >>>= θ)

  ireturn = Var

subst :: v ⇶ w → Term v →° Term w
subst = (=<<<)

-- As with any monad, fmap can be derived from bind and return.
-- This is a bit nasty here though. Indeed the definition of bind
-- uses lift which uses wk which uses fmap.
instance IFunctor Term where
  imap f t = t >>>= ireturn . f

subst0 :: Term v ∪ v →° Term v
subst0 (Inl x) = x
subst0 (Inr x) = Var x

beta :: Term v →° Term v
beta (App (Lam _ t) u) = t u >>>= subst0
beta t = t

data Value v t where
  Clo :: Name → (forall w. w s → Term (w ∪ v) t) → Value v (s → t)

cbn :: Term Zero →° Value Zero
cbn (App t u)  = case cbn t of
                   Clo _ f -> cbn (f u >>>= subst0)
cbn (Lam nm f) = Clo nm f
cbn (Var x)    = magic x
-- -}
-- -}
-- -}
