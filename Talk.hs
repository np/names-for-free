
-- {{{
{-# LANGUAGE RankNTypes, UnicodeSyntax, 
    TypeOperators, GADTs, MultiParamTypeClasses, 
    FlexibleInstances, UndecidableInstances, 
    IncoherentInstances, ScopedTypeVariables #-} 
import Prelude hiding (elem,any)
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Data.List (nub,elemIndex)
-- }}}
-- DeBruijn

-- Exercise: Sxyz = xz(yz)

-- {{{ Nested

data a :> v = There a | Here v
  
instance Eq w ⇒ Eq (w :> v) where
  Here _ == Here _ = True
  There x == There y = x == y
  _ == _ = False

type Succ a = a :> ()

-- }}}
-- {{{ Parametric Nested

data Tm a where
  Var :: a → Tm a
  App :: Tm a → Tm a → Tm a
  Lam :: (∀ v. v → Tm (a :> v)) → Tm a

($$) = App
infixl $$

data Zero
instance Eq Zero where
  (==) = magic

magic :: Zero -> a
magic = error "magic!"

var0 = Var . Here
var1 = Var . There . Here
var2 = Var . There . There . Here

scomb2 :: Tm Zero
scomb2 = Lam $ \x -> Lam $ \y -> Lam $ \z -> var2 x $$ var0 z $$ (var1 y $$ var0 z)
-- }}}
-- {{{ :∈ 

instance x :∈ (γ :> x) where
  inj = Here
  
instance (x :∈ γ) ⇒ x :∈ (γ :> y) where
  inj = There . inj

class v :∈ a where
  inj :: v → a

var :: ∀ v a. (v :∈ a) ⇒ v → Tm a
var = Var . inj

scomb3 = Lam $ \x -> Lam $ \y -> Lam $ \z -> var x $$ var z $$ (var y $$ var z)

-- }}}
-- {{{ Free vars

fv :: Tm a → [a]
fv (Var x) = [x]
fv (Lam f) = rm (freeVars $ f ())
fv (App f a) = freeVars f ++ freeVars a

rm :: [a :> v] → [a]
rm xs = [x | There x <- xs]

occursIn :: (Eq a, v :∈ a) ⇒ v → Tm a → Bool
occursIn x t = any (`isOccurrenceOf` x) (freeVars t)

isOccurrenceOf :: (Eq w, v :∈ w) => w -> v -> Bool
isOccurrenceOf x y = x == inj y

-- }}}
-- {{{ η-contract?
canEta :: Tm Zero → Bool
canEta (Lam e) = unpack e $ \x t → case t of
  App e1 (Var y) → y `isOccurrenceOf` x &&
                   not (x `occursIn` e1)
  _ → False
canEta _ = False
-- }}}
-- {{{ Unpack
unpack :: (∀ v. v → tm (w :> v)) → 
          (∀ v. v → tm (w :> v) → a) → a
unpack b k = k fresh (b fresh)

fresh = error "can't have THAT!"
-- }}}
-- {{{ Exercise: rewrite fv/rm
remove :: v -> [a :> v] → [a]
remove _ xs = [x | There x <- xs]

freeVars :: Tm w → [w]
freeVars (Var x) = [x]
freeVars (Lam f) = unpack f $ \ x t → 
   remove x (freeVars t)
freeVars (App f a) = freeVars f ++ freeVars a
-- }}}
-- {{{ Functor
mapu :: (u → u') → (v → v') → (u :> v) → (u' :> v')
mapu f g (There x) = There (f x)
mapu f g (Here x) = Here (g x)

instance Functor Tm where
  fmap f (Var x) = Var (f x)
  fmap f (Lam g) = Lam (\x -> fmap (mapu f id) (g x))
  fmap f (App t u) = App (fmap f t) (fmap f u)
-- }}}
-- {{{ ⊆
class a ⊆ b where
  injMany :: a → b

instance a ⊆ a where injMany = id

instance Zero ⊆ a where injMany = magic

instance (γ ⊆ δ) ⇒ (γ :> v) ⊆ (δ :> v) where
  injMany = mapu injMany id

instance (a ⊆ c) ⇒ a ⊆ (c :> b) where
  injMany = There . injMany


wk :: (Functor f, γ ⊆ δ) ⇒ f γ → f δ
wk = fmap injMany
-- }}}
-- {{{ Monad

lift θ (There x) = wk (θ x)
lift θ (Here  x) = var x

instance Monad Tm where
  Var x    >>= θ = θ x
  Lam t >>= θ = Lam (\x → t x >>= lift θ)
  App t u  >>= θ = App (t >>= θ) (u >>= θ)

  return = Var

(∙) :: (a -> Tm b) -> Tm a -> Tm b
(∙) = (=<<)

-- var :: (Monad tm, v :∈ a) ⇒ v → tm a
-- var = return . inj

-- lift :: (Functor tm, Monad tm) ⇒ (a -> tm b) → (a :> v) -> tm (b :> v)
-- }}}
-- {{{ Pack

pack :: Functor tm ⇒ v' → tm (w :> v') → (∀ v. v → tm (w :> v))
pack x t = \y → fmap (mapu id (const y)) t

lam' :: v → Tm (w :> v) → Tm w
lam' x t = Lam (pack x t)             
            
-- }}}            
-- {{{ Traversable
       
traverseu :: Functor f ⇒ (a → f a') → (b → f b') →
                              a :> b → f (a' :> b')
traverseu f _ (There x) = There <$> f x
traverseu _ g (Here x) = Here <$> g x

instance Foldable Tm where foldMap = foldMapDefault
instance Traversable Tm where
  traverse f (Var x) =
    Var <$> f x
  traverse f (App t u) =
    App <$> traverse f t <*> traverse f u
  traverse f (Lam g) = 
    unpack g $ \x b → 
      lam' x <$> traverse (traverseu f pure) b
           
-- {{{  Free vars again:    
fv' :: Tm x -> [x]      
fv' = toList      
-- }}}
      
-- }}}           
      


