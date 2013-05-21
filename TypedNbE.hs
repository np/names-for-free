{-# LANGUAGE Rank2Types, UnicodeSyntax, TypeOperators, GADTs #-}
module TypedNbE where

import TypedPNS
import Indexed
import Name
import qualified TypedTerm as T

data Ne a t where
  Var :: a t → Ne a t
  App :: Ne a (s -> t) → No a s → Ne a t

data No a t where
  Lam :: Name → (forall v. v s → No (a :▹ v) t) → No a (s -> t)
  Emb :: Ne a t → No a t

instance IFunctor No where
  imap = liftIM

type a ⇶ b = a →° No b

instance IMonad No where
  ireturn = Emb . Var

  Lam nm t >>>= θ = Lam nm (\x → t x >>>= lift θ)
  Emb t    >>>= θ = θ ==<<< t

(==<<<) :: a ⇶ b → Ne a →° No b
θ ==<<< Var x   = θ x
θ ==<<< App t u = app (θ ==<<< t) (u >>>= θ)

app :: No a (s → t) → No a s → No a t
app (Lam _ t) u = subst0 =<<< t u
app (Emb t)   u = Emb $ App t u

eval :: T.Term a →° No a
eval (T.Var x)   = Emb (Var x)
eval (T.Lam n t) = Lam n (eval . t)
eval (T.App t u) = app (eval t) (eval u)
