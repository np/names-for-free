{-# OPTIONS --no-positivity-check #-}
-- from Bob Atkey
module nbe-hoas where

lamOp : (a : Set) -> Set
lamOp a = (a -> a) -> a

appOp : (a : Set) -> Set
appOp a = a -> a -> a

openHoas : Set -> Set
openHoas a = lamOp a -> appOp a -> a

hoasTerm : Set1
hoasTerm = forall {A} -> openHoas A

mutual
  data neutral (v : Set) : Set where
    V : v -> neutral v
    A : neutral v -> sem v -> neutral v

  data sem (v : Set) : Set where
    L : (sem v -> sem v) -> sem v
    N : neutral v -> sem v

eval : {v : Set} -> hoasTerm -> sem v
eval {v} f = f L helper
  where helper : sem v -> sem v -> sem v
        helper (L f) y = f y
        helper (N n) y = N (A n y)

mutual
  reify : {exp : Set} ->
          lamOp exp ->
          appOp exp ->
          sem exp -> exp
  reify lam app (L f) = lam (\ x -> reify lam app (f (N (V x))))
  reify lam app (N n) = reifyn lam app n

  reifyn : {exp : Set} ->
           lamOp exp -> appOp exp ->
           neutral exp -> exp
  reifyn lam app (V v)   = v
  reifyn lam app (A n d) = app (reifyn lam app n) (reify lam app d)

norm : hoasTerm -> hoasTerm
norm t = \ lam _·_ -> reify lam _·_ (eval t)

t1 : hoasTerm
t1 lam _·_ = (lam \ x -> lam \ y -> x · y) · (lam \ x -> x)

t2 : hoasTerm
t2 lam _·_ = lam \ z -> ((lam \ x -> lam \ y -> x · y) · z) · (lam \ x -> lam \ y -> x · y)

