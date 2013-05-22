{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             EmptyDataDecls, PatternGuards,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings, StandaloneDeriving, KindSignatures, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
module Dual where

import Classy ((:▹)(Here,There),mapu,(:∈)(lk))
import qualified Classy as T

data Tm a where
  Var :: a → Tm a
  Lam :: v → Tm (a :▹ v) → Tm a
  App :: Tm a → Tm a → Tm a

var :: (x :∈ γ) ⇒ x → Tm γ
var = Var . lk

extend :: v' -> (a -> b) -> (a :▹ v) -> (b :▹ v')
extend x f = mapu f (const x)

fromTm :: (a -> b) -> Tm a -> T.Term b
fromTm f (Var x) = T.Var (f x)
fromTm f (App t u) = T.App (fromTm f t) (fromTm f u)
fromTm f (Lam _x b) = T.Lam "" (\y -> fromTm (extend y f) b)

toTm :: (a -> b) -> T.Term a -> Tm b
toTm f (T.Var x)   = Var (f x)
toTm f (T.App t u) = App (toTm f t) (toTm f u)
toTm f (T.Lam _ b) = Lam () (toTm (extend () f) (b ()))

-- Therefore we can give an higher order interface to Lam
lam :: (forall v. v → Tm (a :▹ v)) → Tm a
lam b = Lam () (b ())

-- and an higher order CPS opening...
unLam :: v -> Tm (a :▹ v) ->
         (forall v'. v' -> Tm (a :▹ v') -> b) -> b
unLam x t k = k x t

constTm__ :: Tm a
constTm__ = Lam () (Lam () (Var (There (Here ()))))
-- Using () everywhere defeat the purpose of the technique though...

-- There is an alternative, though:
data X = X
data Y = Y
data Z = Z

constTm_ :: Tm a
constTm_ = Lam X (Lam Y (Var (There (Here X))))

-- Here the types are unambiguous again and one case use the
-- type class search for Here and There
apTm_ :: Tm a
apTm_ = Lam X (Lam Y (App (var X) (var Y)))


data Fresh where
  Fresh :: a -> Fresh

fresh :: Fresh
fresh =  Fresh ()

constTm :: Tm a
constTm =
  case fresh of
  Fresh x ->
    case fresh of
    Fresh y ->
      Lam x (Lam y (var x))

-- Or in CPS style...
fresh' :: (forall v. v -> b) -> b
fresh' k = k ()

apTm :: Tm a
apTm = fresh' $ \x -> fresh' $ \y -> Lam x (Lam y (var x `App` var y))
