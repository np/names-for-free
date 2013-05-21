{-# LANGUAGE Rank2Types, UnicodeSyntax, TypeOperators, KindSignatures #-}
module Indexed where

import Control.Applicative (Const(..))

class Show1 f where
  show1 :: f a -> String

instance Show a => Show1 (Const a) where
  show1 = show . getConst

data Zero a
magic :: Zero a -> b
magic _ = error "magic!"
instance Show (Zero a) where show = magic
instance Show1 Zero where show1 = magic

type f →° g = forall a. f a → g a
newtype IFun f g a = IFun { applyIFun :: f a → g a }

class IFunctor f where
  imap :: (g →° h) → f g →° f h

infixl 1 >>>=
infixr 1 =<<<
class IFunctor f => IMonad f where
  ireturn :: a →° f a
  (=<<<)  :: (a →° f b) → f a →° f b
  (=<<<)  = flip (>>>=)
  (>>>=)  :: f a x → (a →° f b) → f b x
  (>>>=)  = flip (=<<<)

liftIM :: IMonad m => (a →° b) → m a →° m b
liftIM f t = ireturn . f =<<< t

{-
iap :: IMonad m => (forall x. m (IFun g h) x) → m g x → m h x
iap mf mx = mf >>>= \f -> mx >>>= \x -> ireturn (applyIFun f x)

class IFunctor f => IApplicative f where
  ipure :: a →° f a
  (<<*>>) :: f (IFun a b) x → f a x → f b x

newtype WrappedIMonad (m :: (* -> *) -> (* -> *)) a x = WrapIMonad { unwrapIMonad :: m a x }

instance IMonad m => IFunctor (WrappedIMonad m) where
  imap f = WrapIMonad . liftIM f . unwrapIMonad

instance IMonad m => IApplicative (WrappedIMonad m) where
  ipure = WrapIMonad . ireturn
  mf <<*>> mx = WrapIMonad (iapp (unwrapIMonad mf) (unwrapIMonad mx))

class ITraversable t where
 -- itraverse :: IApplicative f => (a →° f b) → t a →° f (t b)
  imapM :: IMonad m => (a →° m b) → t a →° m (t b)
 -- imapM f t = unwrapIMonad $ itraverse (WrapIMonad . f) t
-}
