{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings, StandaloneDeriving, KindSignatures, RankNTypes, TypeFamilies #-}
module Classy where

import Data.String
import Control.Monad (join)

--------------------------------
-- Generic programming prelude

data (:>) a b = There a | Here b 
  deriving Eq
data Zero

type family (:<>) a b 

type instance (:<>) a Zero = a
type instance (:<>) a (b :> v) = (a :<> b) :> b

elim :: (γ -> a) -> (v -> a) -> γ :> v -> a
elim f g (There x) = f x
elim f g (Here x) = g x
  
mapu :: (u -> u') -> (v -> v') -> (u :> v) -> (u' :> v')
mapu f g (There x) = There (f x)
mapu f g (Here x) = Here (g x)                    
                    
deriving instance Eq Zero
magic :: Zero -> a
magic _ = error "magic!"
instance Show Zero where show = magic

instance (Show a, Show b) => Show (a :> b) where
  show (There x) = show x
  show (Here x) = show x

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
  Lam :: Name → (forall w. w → Term (v :> w)) → Term v
  App :: Term v → Term v → Term v

data LL v where
  Ax :: LL (Zero :> v :> w)
  One :: LL (γ :<> δ) -> LL ((γ :> v) :<> δ)
  Cut :: (forall w. w → LL (γ :> w)) -> (forall w. w → LL (δ :> w)) -> LL (γ :<> δ)

var :: forall a γ. (a :∈ γ) => a → Term γ
var = Var . lk

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

cata :: (b -> a) -> ((a -> a) -> a) -> (a -> a -> a) -> Term b -> a
cata fv fl fa (Var x)   = fv x
cata fv fl fa (App f a) = fa (cata fv fl fa f) (cata fv fl fa a)
cata fv fl fa (Lam _ f) = fl (cata (extend fv) fl fa . f)
  
extend g (Here a) = a
extend g (There b) = g b
        
size :: Term Zero -> Int
size = cata magic (\f -> 1 + f 1) (\a b -> 1 + a + b)

-----------------------------------------------------------
-- Terms are monads
-- (which means they support substitution as they should)


wk :: (Functor f, γ :< δ) => f γ -> f δ
wk = fmap inj

-- Kleisli arrows arising from the Term monad
type v :-> w = v → Term w

class x :∈ γ where
  lk :: x -> γ
  
instance x :∈ (γ :> x) where
  lk = Here
  
instance (x :∈ γ) => x :∈ (γ :> y) where
  lk = There . lk


class a :< b where
  inj :: a → b

instance a :< a where
  inj = id

instance Zero :< a where
  inj = magic

instance (γ :< δ) => (γ :> v) :< (δ :> v) where
  inj = mapu inj id

instance (a :< c) => a :< (c :> b) where
  inj = There . inj

instance Functor ((:>) a) where
  fmap _ (There x) = There x
  fmap f (Here x) = Here (f x)


