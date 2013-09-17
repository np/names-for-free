{-# LANGUAGE RankNTypes, UnicodeSyntax,
    TypeOperators, GADTs, MultiParamTypeClasses,
    FlexibleInstances, UndecidableInstances,
    IncoherentInstances, ScopedTypeVariables, ViewPatterns #-}
import Prelude hiding (elem,any)
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Data.List (nub,elemIndex)
import Data.Maybe

data Nat = Zero | Succ Nat
data TmDB where
  VarDB :: Nat → TmDB
  AppDB :: TmDB → TmDB → TmDB
  LamDB :: TmDB → TmDB

constDB :: TmDB
constDB = LamDB $ LamDB $ VarDB (Succ Zero)

data a ▹ v = There a | Here v

type Succ a = a ▹ ()

data Tm a where
  Var :: a → Tm a
  App :: Tm a → Tm a → Tm a
  Lam :: Tm (Succ a) → Tm a


type Univ  tm a = ∀ v.  v -> tm (a ▹ v)
data Exist tm a where 
   N :: v -> tm (a ▹ v) -> Exist tm a
   
type Scope tm a = tm (Succ a) 
   
toUniv :: Functor tm => Scope tm a -> Univ tm a
toUniv t = \x -> fmap (mapu id (const x)) t
 
fromUniv :: Univ tm a -> Scope tm a 
fromUniv f = f ()

toExist :: Scope tm a -> Exist tm a
toExist t = N () t

fromExist :: Functor tm => Exist tm a -> Scope tm a
fromExist (N _ t) = fmap (mapu id (const ())) t


1.

  fromUniv (toUniv t)

== {- def -}
  
  (\x -> fmap (mapu id (const x)) t) ()
  
== {- beta-red -}
  
  fmap (mapu id (const ())) t)

== {- const () == id -}
  
  fmap (mapu id id t)
  
== {- bifunctor law -}
  
   fmap id t

== {- functor law -}

  t


2.

  toUniv (fromUniv t) -> needs param.

3. 

  fromExist (toExist t) 
  
== {- def -}

  fmap (mapu id (const ())) t
  
==  {- as before -} 

  id



lam :: Univ Tm a -> Tm a
lam t = Lam (fromUniv t)
  
constN :: Tm Zero
constN = Lam $ Lam $ Var $ There $ Here ()


data Zero -- no constructor
magic :: Zero → a
magic _ = error "magic!"

constTm_ :: Tm Zero
constTm_ = lam $ \ x → lam $ \ y → 
             Var (There (Here x))

{- --

oops_ = Lam $ \ x → Lam $ \ y → Var (Here x) 
-- Couldn't match expected type `v1' 
--             with actual type `v'

-- -}

class v ∈ a where
  inj :: v → a

{- --

var :: ∀ v a. (v ∈ a) ⇒ v → Tm a
var = Var . inj

-- -}

canEta :: Tm Zero → Bool
canEta (Lam (toExist -> N x (App e1 (Var y)))) = 
  y `isOccurrenceOf` x && not (x `occursIn` e1)

{-
recognize :: Tm Zero → Bool
recognize t0 = case t0 of 
    Lam f → unpack f $ \x t1 → case t1 of
      Lam g → unpack g $ \y t2 → case t2 of
        App e1 (Var y) → y `isOccurrenceOf` x &&
                         not (x `occursIn` e1)
        _ → False   
      _ → False   
    _ → False   
-}
instance Functor Tm where
  fmap f (Var x)   = Var (f x)
  fmap f (Lam g)   = Lam (fmap (mapu f id) g)
  fmap f (App t u) = App (fmap f t) (fmap f u)

{-
{- --

fmap id ≡ id
fmap (f . g) ≡ fmap f . fmap g

-- -}

{- --

fmap id (Var x)
  = Var (id x) = Var x

fmap id (Lam g)
  = Lam (fmap (mapu id id) . g)
  = Lam (fmap id . g)
  = Lam (id . g)
  = Lam g

fmap (f . g) (Var x)
  = Var ((f . g) x)
  = Var (f (g x))
  = fmap f (Var (g x))
  = fmap f (fmap g (Var x))

fmap (f . g) (Lam h)
  = Lam (fmap (mapu (f . g) id) . h)
  = Lam (fmap (mapu f id . mapu g id) . h)
  = Lam (fmap (mapu f id) . fmap (mapu g id) . h)
  = fmap f (Lam (fmap (mapu g id) . h))
  = fmap f (fmap g (Lam h))

-- -}

instance Monad Tm where
  Var x   >>= θ = θ x
  Lam t   >>= θ = Lam (\x → t x >>= lift θ)
  App t u >>= θ = App (t >>= θ) (u >>= θ)

  return = Var

var :: (Monad tm, v ∈ a) ⇒ v → tm a
var = return . inj

subst :: Monad m ⇒ (v → m w) → m v → m w
subst = (=<<)

-- Kleisli arrows
type Kl m v w = v → m w

-- '(▹ v)' is a functor in the category of Kleisli arrows
lift :: (Functor tm, Monad tm) ⇒ Kl tm a b → Kl tm (a ▹ v) (b ▹ v)
lift θ (There x) = fmap There (θ x) -- wk (θ x)
lift θ (Here  x) = return (Here x)     -- var x

-- -}
instance x ∈ (γ ▹ x) where
  inj = Here
  
instance (x ∈ γ) ⇒ x ∈ (γ ▹ y) where
  inj = There . inj
mapu :: (u → u') → (v → v') → (u ▹ v) → (u' ▹ v')
mapu f g (There x) = There (f x)
mapu f g (Here x) = Here (g x)
{-
class a ⊆ b where
  injMany :: a → b

instance a ⊆ a where injMany = id

instance Zero ⊆ a where injMany = magic

instance (γ ⊆ δ) ⇒ (γ ▹ v) ⊆ (δ ▹ v) where
  injMany = mapu injMany id

instance (a ⊆ c) ⇒ a ⊆ (c ▹ b) where
  injMany = There . injMany

wk :: (Functor f, γ ⊆ δ) ⇒ f γ → f δ
wk = fmap injMany
-}
instance Traversable Tm where
  traverse f (Var x) =
    Var <$> f x
  traverse f (App t u) =
    App <$> traverse f t <*> traverse f u
  traverse f (Lam (toExist -> N x b)) = 
      (\t -> Lam (fromExist (N x t))) <$> traverse (traverseu f pure) b

traverseu :: Functor f ⇒ (a → f a') → (b → f b') →
                              a ▹ b → f (a' ▹ b')
traverseu f _ (There x) = There <$> f x
traverseu _ g (Here x)  = Here  <$> g x

instance Foldable Tm where
  foldMap = foldMapDefault
{-
type Size = Int

size2 :: (a -> Size) -> Tm a → Size
size2 ρ (Var _) = 1
size2 ρ (App t u) = 1 + size2 t + size2 u
size2 ρ (Lam g) = unpack g $ \x t -> 1 + size2 ρ' t
 where ρ' (Here _) = 1
       ρ' (There x) = ρ x

size1 :: Tm Size → Size
size1 (Var x) = x
size1 (Lam g) = 1 + size1 (fmap untag (g 1))
size1 (App t u) = 1 + size1 t + size1 u

untag :: a ▹ a → a
untag (There x) = x 
untag (Here x) = x 

size3 :: (Nat → Size) → Tm Nat → Size
size3 f (Var x) = f x
size3 f (Lam g) = 1 + size3 f' (fmap toNat (g ()))
  where f' Zero = 1
        f' (Succ n) = f n
size3 f (App t u) = 1 + size3 f t + size f u

toNat (Here ()) = Zero
toNat (There x) = Succ x

  
size :: (a → Size) → Tm a → Size
size f (Var x) = f x
size f (Lam g) = 1 + size (extend f) (g 1)
size f (App t u) = 1 + size f t + size f u

  
extend g (Here a) = a
extend g (There b) = g b

data TmAlg w a = TmAlg { pVar :: w → a
                       , pLam :: (a → a) → a
                       , pApp :: a → a → a }

cata :: TmAlg w a → Tm w → a
cata φ s = case s of
   Var x   → pVar φ x
   Lam f   → pLam φ (cata (extendAlg φ) . f)
   App t u → pApp φ (cata φ t) (cata φ u)

extendAlg :: TmAlg w a -> TmAlg (w ▹ a) a
extendAlg φ = φ { pVar = extend (pVar φ) }

{- --

unpack :: (∀ v. v → tm (a ▹ v)) →
          (∀ v. v → tm (a ▹ v) → b) → b

-- -}

unpack binder k = k fresh (binder fresh)
  where fresh = ()

pack' :: Functor tm ⇒ tm (a ▹ v) →
                      (∀ w. w → tm (a ▹ w))
pack' t = \y → fmap (mapu id (const y)) t

pack :: Functor tm ⇒ v' → tm (a ▹ v') → 
                     (∀ v. v → tm (a ▹ v))
pack x t = \y → fmap (mapu id (const y)) t

lam :: v → Tm (a ▹ v) → Tm w
lam x t = Lam (pack x t)

freeVars :: Tm w → [w]
freeVars (Var x) = [x]
freeVars (Lam b) = unpack b $ \ x t →
   remove x (freeVars t)
freeVars (App f a) = freeVars f ++ freeVars a

remove :: v -> [a ▹ v] → [a]
remove _ xs = [x | There x <- xs]

freeVars' :: Tm w → [w]
freeVars' = toList
-}

instance Eq Zero where
  (==) = magic

instance Eq w ⇒ Eq (w ▹ v) where
  Here  _ == Here  _ = True
  There x == There y = x == y
  _       == _       = False

isOccurenceOf :: (Eq a, v ∈ a) ⇒ a → v → Bool
x `isOccurenceOf` y = x == inj y

occursIn :: (Eq a, v ∈ a) ⇒ v → Tm a → Bool
x `occursIn` t = inj x `elem` t 

{- 

instance Eq w ⇒ Eq (Tm w) where
  Var x == Var x' = x == x'
  Lam g == Lam g' = g () == g' ()
  App t u == App t' u' = t == t' && u == u'        

{- --

  Lam g == Lam g' = unpack g  $ \x  t  →
                    unpack g' $ \x' t' →
                    t == t'

-- -}

unpack2 :: (∀ v. v → f (a ▹ v)) ->
           (∀ v. v → g (a ▹ v)) ->
            
           (∀ v. v → f (a ▹ v) ->
                       g (a ▹ v) -> b) ->
           b 
unpack2 f f' k = k fresh (f fresh) (f' fresh)          
  where fresh = ()

{- --

  Lam g == Lam g' = unpack2 g g' $ \x t t' -> 
                    t == t'

-- -}

subst0 :: Monad tm ⇒ w ▹ tm w → tm w
subst0 (Here  x) = x
subst0 (There x) = return x

app :: Tm a → Tm a → Tm a
app (Lam t) u = subst0 =<<< t u
app t u = App t u

(=<<<) :: (a -> Tm b) -> Tm a -> Tm b
θ =<<< Var x   = θ x
θ =<<< Lam t   = Lam (\x → lift θ =<<< t x)
θ =<<< App t u = app (θ =<<< t) (θ =<<< u)

eval :: Tm w → Tm w
eval (Var x) = Var x
eval (Lam t) = Lam (eval . t)
eval (App t u) = app (eval t) (eval u)

data LC w where
  VarC :: w → LC w
  AppC :: LC w → LC w → LC w
  Closure :: (∀ vx venv. vx → venv → 
           LC (Zero ▹ venv ▹ vx)) →
           LC w → 
           LC w
  Tuple :: [LC w] → LC w
  Index :: LC w → Int → LC w
  LetOpen :: LC a → 
             (∀ vf venv. vf → venv → 
              LC (a ▹ vf ▹ venv)) → LC a

($$) = AppC
infixl $$

idx :: (v ∈ a) ⇒ v → Int → LC a
idx env = Index (var env)

cc :: ∀ w. Eq w ⇒ Tm w → LC w  
cc (Var x) = VarC x
cc t0@(Lam f) = 
  let yn = nub $ freeVars t0
      bindAll :: ∀env. env -> w -> LC (Zero ▹ env)
      bindAll env = \z → idx env (fromJust $ elemIndex z yn)
  in Closure (\x env → cc (f x) >>= 
                   (lift $ bindAll env))
          (Tuple $ map VarC yn)
cc (App e1 e2) = 
  LetOpen (cc e1)
          (\f x → var f $$ wk (cc e2) $$ var x)

data Tm' a where
  Halt' :: a → Tm' a
  App'  :: a → a → Tm' a
  Let   :: Value a → (∀ w. w → Tm' (a ▹ w)) → Tm' a

data Value a where 
  Abs' :: (∀ w. w → Tm' (a ▹ w)) → Value a 
  Pair :: a → a → Value a 
  Π1   :: a → Value a -- First projection
  Π2   :: a → Value a -- Second projection

pair :: (v ∈ a, v' ∈ a) ⇒ v → v' → Value a 
π1 :: (v ∈ a) ⇒ v → Value a
π2 :: (v ∈ a) ⇒ v → Value a
app' :: (v ∈ a, v' ∈ a) ⇒ v → v' → Tm' a 
halt' :: (v ∈ a) ⇒ v → Tm' a 

cps :: Tm a -> (∀ v. v -> Tm' (a ▹ v)) → Tm' a
cps (Var x)     k = fmap untag (k x)
cps (App e1 e2) k = 
  cps e1 $ \f -> 
  cps (wk e2) $ \x -> 
  Let (Abs' (\x -> wk (k x))) $ \k' → 
  Let (pair x k') $ \p → 
  app' f p
cps (Lam e')    k = 
  Let (Abs' $ \p → Let (π1 p) $ \x → 
                   Let (π2 p) $ \k' →
                   cps (wk (e' x)) $ \r → 
                   app' k' r)
      k

data TmP a where
  VarP :: a -> TmP a
  LamP :: (a -> TmP a) -> TmP a
  AppP :: TmP a -> TmP a -> TmP a

join' (VarP x) = x
join' (LamP f) = LamP (\x -> join' (f (VarP x)))
join' (AppP t u) = AppP (join' t) (join' u)

{- --

lam :: ((∀ n. (Leq (S m) n ⇒ Fin n)) → Tm (S m)) →
         fTm m
var :: Fin n → Tm n

-- -}

{- --

-- Abstract interface
World :: *
Binder :: * 
Name :: World → *
Empty :: World 
(◅) :: Binder → World → World

-- -}

{- --

data Tm α where
  Var :: Name α → Tm α
  App :: Tm α → Tm α → Tm α
  Lam :: (b :: Binder) → Tm (b ◅ α) → Tm α

-- -}

{- --

type Univ  tm a = ∀ v.  v -> tm (a :▹ v)
type Exist tm a = ∃ v. (v ,  tm (a :▹ v))

-- -}

data TmD a where
  VarD :: a -> TmD a
  AppD :: TmD a -> TmD a -> TmD a
  LamD :: v -> TmD (a ▹ v) -> TmD a

freevarsD :: TmD a -> [a]  
freevarsD (LamD x t) = remove x (freevarsD t)

lamD :: (∀ v. v -> TmD (a ▹ v)) -> TmD a
lamD f = unpack f LamD

instance Functor Value where  
  fmap f (Π1 x) = Π1 (f x)
  fmap f (Π2 x) = Π2 (f x)
  fmap f (Pair x y) = Pair (f x) (f y)
  fmap f (Abs' g) = Abs' (\x -> fmap (mapu f id) (g x))
  
instance Functor Tm' where 
  fmap f (Halt' x) = Halt' (f x)
  fmap f (App' x y) = App' (f x) (f y)
  fmap f (Let p g) = Let (fmap f p) (\x -> fmap (mapu f id) (g x))

pair x y = Pair (inj x) (inj y)
π1 = Π1 . inj
π2 = Π2 . inj
app' x y = App' (inj x) (inj y)
halt' = Halt' . inj

instance Functor LC where
  fmap f t = t >>= return . f

instance Monad LC where
  return = VarC
  VarC x >>= θ = θ x
  Closure c env >>= θ = Closure c (env >>= θ)
  LetOpen t g >>= θ = 
    LetOpen (t >>= θ) (\f env -> g f env >>= lift (lift θ))
  Tuple ts >>= θ = Tuple (map (>>= θ) ts)
  Index t i >>= θ = Index (t >>= θ) i
  AppC t u >>= θ = AppC (t >>= θ) (u >>= θ)

packGen :: ∀ f v a b w. (Functor f, Insert v a b) =>
           v -> f b -> (w -> f (a ▹ w))
packGen _ t x = fmap (shuffle cx) t
  where cx :: v -> w
        cx _ = x

class (v ∈ b) => Insert v a b where    
  -- inserting 'v' in 'a' yields 'b'.
  shuffle :: (v -> w) -> b -> a ▹ w

instance Insert v a (a ▹ v) where
  shuffle f (Here x) = Here (f x)
  shuffle f (There x) = There x
  
instance Insert v a b => Insert v (a ▹ v') (b ▹ v') where
  shuffle f (Here x) = There (Here x)
  shuffle f (There x) = case shuffle f x of
    Here y -> Here y
    There y -> There (There y)

-- -}
