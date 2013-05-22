{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             EmptyDataDecls, PatternGuards,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings, StandaloneDeriving, KindSignatures, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
module Dual where

import Classy ((:▹)(Here,There),mapu)
import qualified Classy as T

data Tm a where
  Var :: a → Tm a
  Lam :: v → Tm (a :▹ v) → Tm a
  App :: Tm a → Tm a → Tm a

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

constTm_ :: Tm a
constTm_ = Lam () (Lam () (Var (There (Here ()))))
-- Using () everywhere defeat the purpose of the technique though...

-- There is an alternative, though:
data X = X
data Y = Y
data Z = Z

constTm :: Tm a
constTm = Lam X (Lam Y (Var (There (Here X))))

apTm :: Tm a
apTm = Lam X (Lam Y (App (Var (There (Here X))) (Var (Here Y))))

lam :: (forall v. v → Tm (a :▹ v)) → Tm a
lam b = Lam () (b ())

unLam :: v -> Tm (a :▹ v) ->
         (forall v'. v' -> Tm (a :▹ v') -> b) -> b
unLam x t f = f x t
