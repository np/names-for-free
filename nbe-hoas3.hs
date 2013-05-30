-- starting from nbe-hoas3.agda
--module nbe-hoas3 where
{-# LANGUAGE Rank2Types #-}

{-
class TM a where
  lam :: (a -> a) -> a
  app :: a -> a -> a

-- Open HOAS terms
type OTm a = TM a => a
-}

type OTm a = ((a -> a) -> a) -> (a -> a -> a) -> a

-- Close HOAS terms
type Tm = forall a. OTm a

data Sem v
  = L (Sem v -> Sem v)
  | A (Sem v) (Sem v)
  | V v

eval :: Tm -> Sem v
eval f = f L app' where
  app' (L f) x = f x
  app' f     x = A f x

reify :: Sem exp -> OTm exp
reify s lam app = go s where
  go (L f)   = lam $ go . f . V
  go (A n d) = app (go n) (go d)
  go (V v)   = v

norm :: Tm -> Tm
norm = reify . eval

idTm :: Tm
idTm lam app = lam $ \x -> x

apTm :: Tm
apTm lam app = lam $ \x -> lam $ \y -> x `app` y

t1 :: Tm
t1 lam app = apTm lam app `app` idTm lam app

t2 :: Tm
t2 lam app = lam $ \z -> ((lam $ \x -> lam $ \y -> x `app` y) `app` z) `app` (lam $ \x -> lam $ \y -> x `app` y)

data DB a
  = Var a
  | App (DB a) (DB a)
  | Lam (DB (Maybe a))
  deriving (Show)
data H = H
h = h

newtype D = D { unD :: forall a. a -> DB a }
db :: Tm -> DB ()
db t = unD (t (\g -> D $ \x -> Lam $ unD (g (D Var)) Nothing) (\(D t) (D u) -> D (\x -> App (t x) (u x)))) ()

