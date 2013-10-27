{-# LANGUAGE RankNTypes, UnicodeSyntax,
    TypeOperators, GADTs, MultiParamTypeClasses,
    FlexibleInstances, UndecidableInstances,
    IncoherentInstances, ScopedTypeVariables, StandaloneDeriving #-}
module PaperCode where
import Prelude hiding (elem,any,foldl,foldr)
import Control.Monad
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.List (nub,elemIndex)
import Data.Maybe
-- import Data.Bifunctor 

main :: IO ()
main = putStrLn "It works!"

{- --

-- Building the following term: \ f x → f x
apTm = lam $ \ f → lam $ \ x → var f `App` var x

-- -}

{- --

canEta (Lam e) = unpack e $ \ x t → case t of
  App e1 (Var y) → y `isOccurrenceOf` x &&
                    x `freshFor` e1
  _ → False
canEta _ = False

-- -}

data Nat = O | S Nat
data TmB where
  VarB :: Nat → TmB
  AppB :: TmB → TmB → TmB
  LamB :: TmB → TmB

apB :: TmB
apB = LamB $ LamB $ VarB (S O) `AppB` VarB O

data Tm a where
  Var :: a → Tm a
  App :: Tm a → Tm a → Tm a
  Lam :: Tm (Succ a) → Tm a

  deriving (Show)

type Succ a = a :▹ ()

data a :▹ v  = Old a | New v

mapOld :: (a → a') → (a :▹ v) → (a' :▹ v)
mapOld f (Old x) = Old (f x)
mapOld _ (New x) = New x

mapNew :: (v → v') → (a :▹ v) → (a :▹ v')
mapNew _ (Old x) = Old x
mapNew f (New x) = New (f x)

untag :: a :▹ a → a
untag (Old x) = x
untag (New x) = x

bimap :: (a → a') → (v → v') →
         (a :▹ v) → (a' :▹ v')
bimap f _ (Old x) = Old (f x)
bimap _ g (New x) = New (g x)

deriving instance (Show a, Show b) ⇒ Show (a :▹ b)

apNested :: Tm Zero
apNested = Lam $ Lam $ Var (Old $ New ())
                 `App` Var (New ())

data Zero -- no constructors

lam :: (∀ v. v → Tm (a :▹ v)) → Tm a
lam f = Lam (f ())

apTm_ :: Tm Zero
apTm_ = lam $ \ f → lam $ \ x →
          Var (Old (New f)) `App` Var (New x)

{- --

oops_ = lam $ \ f → lam $ \ x →
          Var (New f) `App` Var (New x)
-- Couldn't match expected type `v1'
--             with actual type `v'

-- -}

class v :∈ a where
  inj :: v → a

{- --

var :: ∀ v a. (v :∈ a) ⇒ v → Tm a
var = Var . inj

-- -}

-- Building the following term: \ f x → f x
apTm = lam $ \ f → lam $ \ x → var f `App` var x

unpack :: f (Succ a) → 
          (∀ v. v → f (a :▹ v) → r) → r
unpack e k = k () e

canEta :: Tm Zero → Bool
canEta (Lam e) = unpack e $ \ x t → case t of
  App e1 (Var y) → y `isOccurrenceOf` x &&
                    x `freshFor` e1
  _ → False
canEta _ = False

recognizeExample :: Tm Zero → Bool
recognizeExample t0 = case t0 of
    Lam f → unpack f $ \ x t1 → case t1 of
      Lam g → unpack g $ \ y t2 → case t2 of
        App e1 (Var z) → z `isOccurrenceOf` x &&
                          x `freshFor` e1 &&
                          y `freshFor` e1
        _ → False
      _ → False
    _ → False

pack :: Functor tm ⇒ v → tm (a :▹ v) → tm (Succ a)
pack x = fmap (mapNew (const ()))

packGen :: ∀ f v a b w. (Functor f, Insert v a b) ⇒
           v → f b → (w → f (a :▹ w))

lamP :: v → Tm (a :▹ v) → Tm a
lamP x t = Lam (pack x t)

remove :: v → [a :▹ v] → [a]
remove _ xs = [x | Old x ← xs]

freeVars_ :: Tm a → [a]
freeVars_ (Var x) = [x]
freeVars_ (Lam b) = unpack b $ \ x t →
   remove x (freeVars_ t)
freeVars_ (App f a) = freeVars_ f ++ freeVars_ a

instance Eq Zero where
  (==) = magic

magic :: Zero → a
magic _ = error "impossible"

instance Eq a ⇒ Eq (a :▹ v) where
  New _ == New _ = True
  Old x == Old y = x == y
  _     == _     = False

deriving instance Eq a ⇒ Eq (Tm a)

instance v :∈ (a :▹ v) where
  inj = New

instance (v :∈ a) ⇒ v :∈ (a :▹ v') where
  inj = Old . inj

isOccurrenceOf :: (Eq a, v :∈ a) ⇒ a → v → Bool
x `isOccurrenceOf` y = x == inj y

freshFor_ :: (Eq a, v :∈ a) ⇒ v → Tm a → Bool
x `freshFor_` t = not (inj x `elem` freeVars_ t)

class a :⊆ b where
  injMany :: a → b

instance a :⊆ a where injMany = id

instance Zero :⊆ a where injMany = magic

instance (a :⊆ b) ⇒ a :⊆ (b :▹ v) where
  injMany = Old . injMany

instance (a :⊆ b) ⇒ (a :▹ v) :⊆ (b :▹ v) where
  injMany = mapOld injMany

instance Functor Tm where
  fmap f (Var x)   = Var (f x)
  fmap f (Lam b)   = unpack b $ \ x t →
                       lamP x $ fmap (mapOld f) t
  fmap f (App t u) = App (fmap f t) (fmap f u)

{- --

fmap id ≡ id
fmap (f . g) ≡ fmap f . fmap g

-- -}

rename0 :: Eq a ⇒ (a, a) → a → a
rename0 (x,y) z | z == x    = y
                | otherwise = z

rename :: (Functor f, Eq a) ⇒ (a, a) → f a → f a
rename = fmap . rename0

swap0 :: Eq a ⇒ (a, a) → a → a
swap0 (x,y) z | z == y    = x
              | z == x    = y
              | otherwise = z

swap :: (Functor f, Eq a) ⇒ (a, a) → f a → f a
swap = fmap . swap0

wk :: (Functor f, a :⊆ b) ⇒ f a → f b
wk = fmap injMany

instance Monad Tm where
  return = Var
  Var x   >>= θ = θ x
  Lam s   >>= θ = Lam (s >>>= θ)
  App t u >>= θ = App (t >>= θ) (u >>= θ)

liftSubst :: (Functor tm, Monad tm) ⇒
          v → (a → tm b) → (a :▹ v) → tm (b :▹ v)
liftSubst _ θ (Old x) = fmap Old (θ x)
liftSubst _ θ (New x) = return (New x)

(>>>=) :: (Functor tm, Monad tm) ⇒
          tm (Succ a) → (a → tm b) → tm (Succ b)
s >>>= θ = unpack s $ \ x t →
             pack x (t >>= liftSubst x θ)

var :: (Monad tm, v :∈ a) ⇒ v → tm a
var = return . inj

substitute :: (Monad tm, Eq a, v :∈ a) ⇒
              v → tm a → tm a → tm a
substitute x t u = u >>= \ y →
     if y `isOccurrenceOf` x then t else return y

substituteOut :: Monad tm ⇒
                 v → tm a → tm (a :▹ v) → tm a
substituteOut x t u = u >>= \ y → case y of
     New _ → t
     Old x → return x

instance Traversable Tm where
  traverse f (Var x)   = Var <$> f x
  traverse f (App t u) =
    App <$> traverse f t <*> traverse f u
  traverse f (Lam t)   =
    unpack t $ \ x b →
      lamP x <$> traverse (bitraverse f pure) b

bitraverse :: Functor f ⇒ (a     → f a')
                        → (b     → f b')
                        → (a :▹ b → f (a' :▹ b'))
bitraverse f _ (Old x) = Old <$> f x
bitraverse _ g (New x) = New <$> g x

closed :: Traversable tm ⇒ tm a → Maybe (tm b)
closed = traverse (const Nothing)

freeVars :: Tm a → [a]
freeVars = toList

freshFor :: (Eq a, v :∈ a) ⇒ v → Tm a → Bool
x `freshFor` t = not (inj x `elem` t)

type SuccScope tm a = tm (Succ a)

type UnivScope f a = ∀ v. v → f (a :▹ v)

{- --

type UnivScope  tm a = ∀ v.  v → tm (a :▹ v)
type ExistScope tm a = ∃ v. (v ,  tm (a :▹ v))

-- -}

data ExistScope tm a where
  E :: v → tm (a :▹ v) → ExistScope tm a

succToUniv :: Functor tm ⇒
              SuccScope tm a → UnivScope tm a
succToUniv t = \ x → mapNew (const x) <$> t

univToSucc :: UnivScope tm a → SuccScope tm a
univToSucc f = f ()

{- --

   univToSucc (succToUniv t)
 ≡ {- by def -}
   univToSucc (\ x → mapNew (const x) <$> t)
 ≡ {- by def -}
   mapNew (const ()) <$> t
 ≡ {- by () having just one element -}
   mapNew id <$> t
 ≡ {- by (bi)functor laws -}
   t

-- -}

{- --

 ∀ v₁:*.  ∀ v₂:*. ∀ v:v₁ → v₂.
 ∀ x₁:v₁. ∀ x₂:*. v x₁ ≡ x₂.
 ∀ g:(a :▹ v₁) → (a :▹ v₂).
 (∀ y:v₁. New (v y) ≡ g (New y)) →
 (∀ n:a.  Old n     ≡ g (Old n)) →
 f x₂ ≡ g <$> f x₁

-- -}

{- --

f x ≡ mapNew (const x) <$> f ()

-- -}

{- --

   f
 ≡ {- by the above -}
   \ x → mapNew (const x) <$> f ()
 ≡ {- by def -}
   succToUniv (f ())
 ≡ {- by def -}
   succToUniv (univToSucc f)

-- -}

succToExist :: SuccScope tm a → ExistScope tm a
succToExist = E ()

existToSucc :: Functor tm ⇒
               ExistScope tm a → SuccScope tm a
existToSucc (E _ t) = mapNew (const ()) <$> t

{- --

succToExist (existToSucc (E y t)) ≡
  E () (fmap (mapNew (const ())) t)

-- -}

{- --

 ∀ v₁:*.  ∀ v₂:*. ∀ v:v₁ → v₂.
 ∀ x₁:v₁. ∀ x₂:*. v x₁ ≡ x₂.
 ∀ t₁:tm (a :▹ v₁). ∀ t₂:tm (a :▹ v₂).
 (∀ g:(a :▹ v₁) → (a :▹ v₂).
  (∀ y:v₁. New (v y) ≡ g (New y)) →
  (∀ n:a.  Old n     ≡ g (Old n)) →
  t₂ ≡ fmap g t₁) →
 o x₂ t₂ ≡ o x₁ t₁

-- -}

type FunScope tm a = ∀ b. (a → b) → tm b → tm b

fmapFunScope :: (a → b) → FunScope tm a → FunScope tm b
fmapFunScope f g h x = g (h . f) x

returnFunScope :: Monad tm ⇒ a → FunScope tm a
returnFunScope x f t = return (f x)

bindSuccScope :: Monad tm ⇒ (a → SuccScope tm b) →
                   SuccScope tm a → SuccScope tm b
bindSuccScope f t = t >>= \ x → case x of
  Old y  → f y
  New () → return (New ())

-- NP: I started this one by converting to
-- SuccScope, but so far I'm stuck here
bindFunScope :: Monad tm ⇒ (a → FunScope tm b) →
                  FunScope tm a → FunScope tm b
bindFunScope f t g u =
  funToUniv t u >>= \ x → case x of
    New y → y
    Old y → f y g u

existToFun :: Monad tm ⇒ ExistScope tm a
                       → FunScope tm a
existToFun (E x t) f u = t >>= extend (x, u) (return . f)

funToUniv :: Monad tm ⇒ FunScope tm a
                      → UnivScope tm a
funToUniv f = f Old . return . New

-- funToSucc is a special case of funToUniv
funToSucc :: Monad tm ⇒ FunScope tm a
                      → SuccScope tm a
funToSucc f = funToUniv f ()

-- succToFun is a special case of existToFun
succToFun :: Monad tm ⇒ SuccScope tm a
                      → FunScope tm a
succToFun = existToFun . E ()

{- --

fmap' f (Lam b)
   = unpack b $ \ x t → lamP x (mapOld f <$> t)
fmap' f (Lam b)
   = lam (\ x → mapOld f <$> (b `atVar` x))

-- -}

atVar = succToUniv

data No a where
  LamNo :: v → No (a :▹ v) → No a
  Neutr :: a → [No a] → No a

instance Monad No where
  return x = Neutr x []
  LamNo x t  >>= θ = LamNo x (t >>= liftSubst x θ)
  Neutr f ts >>= θ = foldl app (θ f)((>>= θ)<$>ts)

app :: No a → No a → No a
app (LamNo x t)  u = substituteOut x u t
app (Neutr f ts) u = Neutr f (ts++[u])

norm :: Tm a → No a
norm (Var x)   = return x
norm (App t u) = app (norm t) (norm u)
norm (Lam b)   = unpack b $ \ x t →
                   LamNo x (norm t)

data TmS a where
  LamS :: (∀ b. (a → b) → TmS b → TmS b) → TmS a
  VarS :: a → [TmS a] → TmS a

evalS :: (a → TmS b) → Tm a → TmS b
evalS f (Var x)   = f x
evalS f (Lam b)   = unpack b $ \ x t →
                    LamS $ \ g u →
                      evalS (extend (x, u) (fmap g . f)) t
evalS f (App t u) = appS (evalS f t) (evalS f u)

instance Functor TmS where
  fmap f (LamS g)    = LamS $ \ h x → g (h . f) x
  fmap f (VarS x ts) = VarS (f x) (map (fmap f) ts)

varS :: a → TmS a
varS x = VarS x []

appS :: TmS a → TmS a → TmS a
appS (LamS f)    u = f id u
appS (VarS x ts) u = VarS x (ts++[u])

reify :: TmS a → No a
reify (VarS x ts) = Neutr x (map reify ts)
reify (LamS f)    = lamNo $ \ x →
                      reify (f Old (varS (New x)))

nbe :: Tm a → No a
nbe = reify . evalS varS

data TmM a where
  LamM :: (∀ b. (a → TmM b) → TmM b → TmM b) → TmM a
  VarM :: a → [TmM a] → TmM a

-- Unlike TmS, TmM supports a simple monad instance
instance Monad TmM where
  return x = VarM x []
  LamM f    >>= θ = LamM $ f . (<=< θ)
  VarM x ts >>= θ = foldl appM (θ x)((>>= θ)<$>ts)

instance Functor TmM where
  fmap f (LamM g)    = LamM $ \ h x → g (h . f) x
  fmap f (VarM x ts) = VarM (f x) (map (fmap f) ts)

appM :: TmM a → TmM a → TmM a
appM (LamM f)    u = f return u
appM (VarM x ts) u = VarM x (ts++[u])

evalM :: (a → TmM b) → Tm a → TmM b
evalM f (Var x)   = f x
evalM f (Lam b)   = unpack b $ \ x t →
                    LamM $ \ g u →
                     evalM (extend (x, u) (g <=< f)) t
evalM f (App t u) = appM (evalM f t) (evalM f u)

type ScopeM f a = ∀ b. (a → f b) → f b → f b
unpackM :: ScopeM TmM a → (∀ v. v → TmM (a :▹ v) → r) → r
unpackM s k = k () (s `atVarM` ())

-- same as mesToUniv
atVarM :: ScopeM TmM a → v → TmM (a :▹ v)
s `atVarM` x = s (return . Old) (return (New x))

reifyM :: TmM a → No a
reifyM (VarM x ts) = Neutr x (map reifyM ts)
reifyM (LamM s)    = unpackM s $ \ x t →
                       LamNo x (reifyM t)

nbeM :: Tm a → No a
nbeM = reifyM . evalM return

data LC a where
  VarLC :: a → LC a
  AppLC :: LC a → LC a → LC a
  Closure :: (∀ vx venv. vx → venv →
           LC (Zero :▹ venv :▹ vx)) →
           LC a → LC a
  Tuple :: [LC a] → LC a
  Index :: LC a → Int → LC a
  LetOpen :: LC a → (∀ vf venv. vf → venv →
                     LC (a :▹ vf :▹ venv)) → LC a

($$) = AppLC
infixl $$

cc :: Eq a ⇒ Tm a → LC a
cc (Var x) = VarLC x
cc t0@(Lam b) =
  let yn = nub $ freeVars t0
  in Closure (\ x env → cc (b `atVar` x) >>=
                   liftSubst x (idxFrom yn env))
             (Tuple $ map VarLC yn)
cc (App e1 e2) =
  LetOpen (cc e1)
          (\ f x → var f $$ wk (cc e2) $$ var x)

data TmC a where
  HaltC :: Value a → TmC a
  AppC  :: Value a → Value a → TmC a
  LetC  :: Value a → TmC (Succ a) → TmC a

data Value a where
  LamC  :: TmC (Succ a) → Value a
  PairC :: Value a → Value a → Value a
  VarC  :: a → Value a
  FstC  :: a → Value a
  SndC  :: a → Value a

varC :: (v :∈ a) ⇒ v → Value a
letC :: Value a → UnivScope TmC a → TmC a
lamC :: UnivScope TmC a → Value a
fstC :: (v :∈ a) ⇒ v → Value a
sndC :: (v :∈ a) ⇒ v → Value a

cps :: Tm a → (∀ v. v → TmC (a :▹ v)) → TmC a
cps (Var x)     k = untag <$> k x
cps (App e1 e2) k =
  cps e1 $ \ x1 →
  cps (wk e2) $ \ x2 →
  varC x1 `AppC` (varC x2 `PairC`
                  lamC (\ x → wk $ k x))
cps (Lam e)    k =
  letC
    (lamC $ \p →
       letC (fstC p) $ \ x1 →
       letC (sndC p) $ \ x2 →
       cps (wk $ e `atVar` x1) $ \r →
       varC x2 `AppC` varC r) k

data TmH = LamH (TmH → TmH) | AppH TmH TmH

type TmF = ∀ a. ({-lam:-} (a → a) → a)
             → ({-app:-}  a → a  → a) → a

apTmF :: TmF
apTmF lam app = lam $ \ f → lam $ \ x → f `app` x

data TmP a where
  VarP :: a → TmP a
  LamP :: (a → TmP a) → TmP a
  AppP :: TmP a → TmP a → TmP a

type TmP' = ∀ a. TmP a

joinP :: TmP (TmP a) → TmP a

joinP (VarP x)   = x
joinP (LamP f)   = LamP (\ x → joinP (f (VarP x)))
joinP (AppP t u) = AppP (joinP t) (joinP u)

{- --

lam :: ((∀ n. (Leq (S m) n ⇒ Fin n)) → Tm (S m))
       → Tm m
var :: Fin n → Tm n

-- -}

{- --

World :: *
Binder :: *
Empty :: World
(◅) :: Binder → World → World
Name :: World → *

-- -}

{- --

data Tm α where
  Var :: Name α → Tm α
  App :: Tm α → Tm α → Tm α
  Lam :: (b :: Binder) → Tm (b ◅ α) → Tm α

-- -}

type NScope n tm a = tm (a :▹ n)

{- --

type NUnivScope  n tm a = ∀v. (n → v) → tm (a :▹ v)
type NExistScope n tm a = ∃v.((n → v) , tm (a :▹ v))

-- -}

type DelayedScope tm a = tm (tm a :▹ ())

data TmD a where
  VarD :: a → TmD a
  LamD :: DelayedScope TmD a → TmD a
  AppD :: TmD a → TmD a → TmD a

instance Monad TmD where
  return = VarD
  VarD a   >>= θ = θ a
  AppD a b >>= θ = AppD (a >>= θ) (b >>= θ)
  LamD t   >>= θ = LamD (mapOld (>>= θ) <$> t)

instance Functor TmD where
  fmap = liftM

{- --

type UnivScope'  tm a = ∀v. (v → tm (tm a :▹ v))
type ExistScope' tm a = ∃v. (v ,  tm (tm a :▹ v))

-- -}

{- --

type UnivScope  tm a = ∇ v.  v → tm (a :▹ v)
type ExistScope tm a = ∇ v. (v ,  tm (a :▹ v))

-- -}

instance Foldable Tm where
  foldMap = foldMapDefault

extend :: (v, r) → (a → r) → (a :▹ v → r)
extend (_, x) _ (New _) = x
extend _      f (Old x) = f x

instance Functor No where 
  fmap f (LamNo x t)  = 
     LamNo x (fmap (mapOld f) t)
  fmap f (Neutr x ts) =
     Neutr (f x) (fmap (fmap f) ts)

lamNo :: (∀ v. v → No (a :▹ v)) → No a
lamNo f = LamNo () (f ())

instance Functor Value where
  fmap f (VarC x)      = VarC (f x)
  fmap f (FstC x)      = FstC (f x)
  fmap f (SndC x)      = SndC (f x)
  fmap f (PairC v1 v2) = 
     PairC (fmap f v1) (fmap f v2)
  fmap f (LamC t)      =
     LamC (fmap (mapOld f) t)

instance Functor TmC where
  fmap f (HaltC v)    = HaltC (fmap f v)
  fmap f (AppC v1 v2) = 
     AppC  (fmap f v1) (fmap f v2)
  fmap f (LetC p t)   = 
     LetC (fmap f p) (fmap (mapOld f) t)

letC p f = LetC p (f ())
varC = VarC . inj
lamC f = LamC (f ())
fstC = FstC . inj
sndC = SndC . inj

cps0 :: Tm a → TmC a
cps0 t = cps t $ HaltC . varC

idxFrom :: Eq a ⇒ [a] → v → a → LC (Zero :▹ v)
idxFrom yn env z = Index (var env) $
                   fromJust (elemIndex z yn)

instance Functor LC where
  fmap f t = t >>= return . f

instance Monad LC where
  return = VarLC
  VarLC x >>= θ = θ x
  Closure c env >>= θ = Closure c (env >>= θ)
  LetOpen t g >>= θ = LetOpen (t >>= θ) 
    (\ f env → g f env >>= 
        liftSubst env (liftSubst f θ))
  Tuple ts >>= θ = Tuple (map (>>= θ) ts)
  Index t i >>= θ = Index (t >>= θ) i
  AppLC t u >>= θ = AppLC (t >>= θ) (u >>= θ)

packGen _ t x = fmap (shuffle cx) t
  where cx :: v → w
        cx _ = x

class (v :∈ b) ⇒ Insert v a b where
  -- inserting 'v' in 'a' yields 'b'.
  shuffle :: (v → w) → b → a :▹ w

instance Insert v a (a :▹ v) where
  shuffle f (New x) = New (f x)
  shuffle f (Old x) = Old x

instance Insert v a b ⇒ 
         Insert v (a :▹ v') (b :▹ v') where
  shuffle f (New x) = Old (New x)
  shuffle f (Old x) = case shuffle f x of
    New y → New y
    Old y → Old (Old y)

substituteGen :: 
   (Insert v a b, Functor tm, Monad tm) ⇒ 
   v → tm a → tm b → tm a
substituteGen x t u = 
   substituteOut x t (fmap (shuffle id) u)

-- -}

-- -}

-- -}

-- -}

-- -}


