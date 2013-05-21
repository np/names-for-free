{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             OverlappingInstances, IncoherentInstances,
             UnicodeSyntax, TypeOperators, KindSignatures #-}
module TypedPNS where

import Indexed

--------------------------------
-- Generic programming prelude

data (:▹) f g a = There (f a) | Here (g a)

mapu :: (u →° u') -> (v →° v') -> (u :▹ v) →° (u' :▹ v')
mapu f _ (There x) = There (f x)
mapu _ g (Here x)  = Here (g x)

instance IFunctor ((:▹) f) where
  imap f = mapu id f

instance (Show1 f, Show1 g) => Show1 (f :▹ g) where
  show1 (Here  x) = show1 x
  show1 (There x) = show1 x

class f :∈ g where
  lk :: f →° g

instance x :∈ (γ :▹ x) where
  lk = Here

instance (x :∈ γ) => x :∈ (γ :▹ y) where
  lk = There . lk

class a :< b where
  inj :: a →° b

instance a :< a where inj = id

instance Zero :< a where inj = magic

instance (γ :< δ) => (γ :▹ v) :< (δ :▹ v) where inj = mapu inj id

instance (a :< c) => a :< (c :▹ b) where
  inj = There . inj

wk :: IFunctor tm => tm a →° tm (a :▹ v)
wk = imap There

-- IKleisli
type Subst (tm :: (* → *) → (* → *)) a b = a →° tm b

lift :: IMonad tm => Subst tm a b → Subst tm (a :▹ v) (b :▹ v)
lift θ (There x) = wk (θ x)
lift _ (Here x)  = ireturn (Here x)

subst :: IMonad tm => Subst tm a b → tm a →° tm b
subst = (=<<<)

subst0 :: IMonad tm => Subst tm (a :▹ tm a) a
subst0 (Here x)  = x
subst0 (There x) = ireturn x
