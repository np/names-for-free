{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings #-}
module TypedTerm where
import TypedPNS
import Indexed
import Name
import Control.Applicative (Const(..))

----------------------------------------
-- Term representation and examples

data Term a t where
  Var :: a t → Term a t
  Lam :: Name → (forall v. v s → Term (a :▹ v) t)
              → Term a (s → t)
  App :: Term a (s → t) → Term a s → Term a t

var :: (v :∈ a) => v t → Term a t
var = Var . lk

lam :: Name → (forall v. v s → Term (a :▹ v) t)
            → Term a (s → t)
lam = Lam

id' :: Term Zero (a → a)
id' = lam "x" (\x → var x)

const' :: Term Zero (a → b → a)
const' = lam "x" (\x → lam "y" (\_y → var x))

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

type a ⇶ b = Subst Term a b

instance IMonad Term where
  Var x    >>>= θ = θ x
  Lam nm t >>>= θ = Lam nm (\x → t x >>>= lift θ)
  App t u  >>>= θ = App (t >>>= θ) (u >>>= θ)

  ireturn = Var

-- As with any monad, fmap can be derived from bind and return.
-- This is a bit nasty here though. Indeed the definition of bind
-- uses lift which uses wk which uses fmap.
instance IFunctor Term where
  imap = liftIM

beta :: Term v →° Term v
beta (App (Lam _ t) u) = t u >>>= subst0
beta t = t
