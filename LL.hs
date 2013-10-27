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

{-
  NP: extracted somehow from the LL type below

  Ax  :: --------
         ⊢ A , B

  One :: ⊢ Γ ♦ Δ
         -------------
         ⊢ (Γ , A) ♦ Δ

  Cut :: ⊢ Γ , A
         ⊢ Δ , B
         -----------
         ⊢ Γ ♦ Δ
-}

data LL v where
  Ax :: LL (Zero :> v :> w)
  One :: LL (γ :<> δ) -> LL ((γ :> v) :<> δ)
  Cut :: (forall w. w → LL (γ :> w)) -> (forall w. w → LL (δ :> w)) -> LL (γ :<> δ)

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


