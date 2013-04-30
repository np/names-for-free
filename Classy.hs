{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings, StandaloneDeriving, KindSignatures, RankNTypes #-}
module Classy where

import Data.String
import Control.Monad (join)

--------------------------------
-- Generic programming prelude

data (:▹) a b = There a | Here b 
data Zero

elim :: (γ -> a) -> (v -> a) -> γ :▹ v -> a
elim f g (There x) = f x
elim f g (Here x) = g x
  
deriving instance Eq Zero
magic :: Zero -> a
magic _ = error "magic!"
instance Show Zero where show = magic

instance (Show a, Show b) => Show (a :▹ b) where
  show (There x) = show x
  show (Here x) = show x

-------------------------------------------
-- Names as a simple wrapper around strings

newtype Name = Name { unName :: String }

-- Show them without quotes
instance Show Name where
  show = unName

instance IsString Name where
  fromString = Name . fromString

----------------------------------------
-- Term representation and examples

data Term v where
  Var :: v → Term v
  Lam :: Name → (forall w. w → Term (v :▹ w)) → Term v
  App :: Term v → Term v → Term v
   

var :: forall a γ. (a :∈ γ) => a → Term γ
var = Var . lk

lam = Lam

id' :: Term Zero
id' = lam "x" (\x → var x)

const' :: Term Zero
const' = lam "x" (\x → lam "y" (\y → var x))

-- oops' = lam "x" (\x → lam "y" (\y → Var (Here x)))

---------------------
-- Display code

instance Show x => Show (Term x) where
  show = disp

disp :: Show x => Term x → String
disp (Var x)    = show x
disp (App a b)  = "(" ++ disp a ++ ")" ++ disp b
disp (Lam nm f) = "λ" ++ unName nm ++ "." ++ disp (f nm)

---------------------
-- Catamorphism

cata :: (b -> a) -> ((a -> a) -> a) -> (a -> a -> a) -> Term b -> a
cata fv fl fa (Var x)   = fv x
cata fv fl fa (App f a) = fa (cata fv fl fa f) (cata fv fl fa a)
cata fv fl fa (Lam _ f) = fl (cata (extend fv) fl fa . f)
  
extend g (Here a) = a
extend g (There b) = g b
        
-----------------------------------------------------------
-- Terms are monads
-- (which means they support substitution as they should)


wk :: (Functor f, γ :< δ) => f γ -> f δ
wk = fmap inj

-- Kleisli arrows arising from the Term monad
type v :=> w = v → Term w

-- Union is a functor in the category of Kleisli arrows (:=>)
lift :: v :=> w → (v :▹ x) :=> (w :▹ x)
lift θ (There x) = wk (θ x)
lift _ (Here x) = var x

instance Monad Term where
  Var x    >>= θ = θ x
  Lam nm t >>= θ = Lam nm (\x → t x >>= lift θ)
  App t u  >>= θ = App (t >>= θ) (u >>= θ)

  return = Var

subst :: v :=> w → Term v → Term w
subst = (=<<)

-- As with any monad, fmap can be derived from bind and return.
-- This is a bit nasty here though. Indeed the definition of bind
-- uses lift which uses wk which uses fmap.
instance Functor Term where
  fmap f t = t >>= return . f

-- Substitute in an open term
subst' :: (∀v. v → Term v) → Term w → Term w
subst' t u = join (t u)

{-
-- Nbe (HOAS-style)
eval :: Term v -> Term v
eval (Var x) = Var x
eval (Lam n t) = Lam n (eval . t)
eval (App t u) = app (eval t) (eval u)

app :: Term v -> Term v -> Term v
app (Lam _ t) u = subst0 =<< t u 
app t u = App t u

(@@) :: (∀ w. w -> Term (v :▹ w)) -> Term v -> Term v
t @@ u = subst0 =<< t u

subst0 :: v :▹ Term v -> Term v
subst0 (Here x) = x
subst0 (There x) = Var x


(>>=-) :: Term γ -> (γ -> Term δ) -> Term δ
Var x    >>=- θ = θ x
Lam nm f >>=- θ = with f $ \(_,t) -> Lam nm (\x -> t >>=- lift' x θ)
App t u  >>=- θ = App (t >>=- θ) (u >>=- θ)

lift' :: x -> v :=> w → (v :▹ Zero) :=> (w :▹ x)
lift' _ θ (There x) = wk (θ x)
lift' x _ (Here _) = var x 
-}

{-
data Ne v where
  Var' :: v → Ne v
  App' :: Ne v → No v → Ne v

data No v where
  Lam':: Name → (forall w. w → No (w :▹ v)) → No v
  Emb' :: Ne v -> No v

eval :: Term v -> No v
eval (Var x) = Emb' (Var' x)
eval (Lam n t) = Lam' n (eval . t)
eval (App t u) = app (eval t) (eval u)

instance Monad No where
  return = Emb' . Var'

app :: No v -> No v -> No v
app (Lam' _ t) u = yak =<< t u -- t u :: No (No v :▹ v)
app (Emb' t) u = Emb' $ App' t u

yak :: No v :▹ v -> No v
yak (There x) = x
yak (Here x) = Emb' (Var' x)
-}

-------------------
-- Size

sizeHO :: (a -> Int) -> Term a -> Int
sizeHO f (Var x) = f x
sizeHO f (Lam _ g) = 1 + sizeHO (extend f) (g 1)
sizeHO f (App t u) = 1 + sizeHO f t + sizeHO f u

sizeFO :: Term a -> Int
sizeFO (Var _) = 1
sizeFO (Lam _ g) = 1 + sizeFO (g ())
sizeFO (App t u) = 1 + sizeFO t + sizeFO u

sizeC :: Term Zero -> Int
sizeC = cata magic (\f -> 1 + f 1) (\a b -> 1 + a + b)

-----------------------
-- Can eta contract ?

untag :: a :▹ a -> a
untag (There x) = x 
untag (Here x) = x 

{-

(P)HOAS-style

canEta' :: Term Bool -> Bool
canEta' (Var b) = b
canEta' (App e1 e2) = canEta' e1 && canEta' e2
canEta' (Lam _ e') = canEta' (fmap untag $ e' True)


canEta :: Term Bool -> Bool
canEta (Lam _ e') = case fmap untag $ e' False of
  App e1 (Var False) -> canEta' e1
  _ -> False
canEta _ = False

canη :: Term Zero -> Bool
canη = canEta . fmap magic

-}


-- DeBrujn-style (?)
{-
openTerm :: Functor f => (forall w. w → f (v :▹ w)) -> v -> f v
openTerm b x = fmap (elim id (const x)) (b fresh)
  where fresh = error "cannot identify fresh variables!"
-}
    
with :: (forall v. v → f (w :▹ v)) -> (forall v. (v,f (w :▹ v)) -> a) -> a
with b k = k (fresh,(b fresh))
  where fresh = error "cannot query fresh variables!"

instance Eq w => Eq (w :▹ v) where
  Here _ == Here _ = True
  There x == There y = x == y
  _ == _ = False

  
memberOf :: Eq w => w -> Term w -> Bool
memberOf x t = x `elem` freeVars t

rm :: [v :▹ a] -> [v]
rm xs = [x | There x <- xs]

freeVars :: Term w -> [w]
freeVars (Var x) = [x]
freeVars (Lam _ f) = with f $ \ (_,t) -> rm $ freeVars t
freeVars (App f a) = freeVars f ++ freeVars a

canEta :: Term Zero -> Bool
canEta (Lam _ e) = with e $ \(x,t) -> case t of
  App e1 (Var y) -> lk x == y && not (lk x `memberOf` e1)
  _ -> False
canEta _ = False


-- recognizer of \x -> \y -> f x
recognize :: Term Zero -> Bool
recognize t0 = case t0 of 
    Lam _ f -> with f $ \(x,t1) -> case t1 of
      Lam _ g -> with g $ \(y,t2) -> case t2 of
        (App func (Var arg)) -> arg == lk x && not (lk x `memberOf` func)
        _ -> False   
      _ -> False   
    _ -> False   


-------------
-- α-eq

fresh :: Zero
fresh = error "cannot access free variables"


instance Eq a => Eq (Term a) where
  Var x == Var x' = x == x'
  Lam _ g == Lam _ g' = -- with g $ \(_,t) -> with g' $ \(_,t') -> t == t'
                        g fresh == g' fresh
  App t u == App t' u' = t == t' && u == u'        

-------------
-- CPS

data Primop v :: * where 
--  Tru' :: Primop v
--  Fals' :: Primop v
  Var' :: v -> Primop v
  Abs' :: (∀ w. w -> Term' (v :▹ w)) -> Primop v
  (:-) :: v -> v -> Primop v  -- Pair
  Π1   :: v -> Primop v
  Π2   :: v -> Primop v


data Term' v where
  Halt' :: v -> Term' v
  App'  :: v -> v -> Term' v
  Let   :: Primop v -> (∀ w. w -> Term' (v :▹ w)) -> Term' v
  
instance Functor Term' where 
  

mapu :: (u -> u') -> (v -> v') -> (u :▹ v) -> (u' :▹ v')
mapu f g (There x) = There (f x)
mapu f g (Here x) = Here (g x)

  
spliceAbs :: ∀ v   .
             (forall w. w  → Term' (v :▹ w) ) -> 
             (∀ w. w  → Term' (v :▹ w) ) -> 
             forall w. w  → Term' (v :▹ w) 
spliceAbs e' e2 x = splice (e' x) (\ x₁ → fmap (mapu There id) (e2 x₁))

-- in e1, substitude Halt' by an arbitrary continuation e2
splice :: forall v  .
         Term' v  ->
         (∀ w. w  -> Term' (v :▹ w) ) -> 
         Term' v 
splice (Halt' v) e2 =  fmap untag (e2 v)
splice (App' f x) e2 = App' f x
splice (Let p e') e2 = Let (splicePrim p e2)  ( spliceAbs e' e2 )

splicePrim :: forall v. Primop v  ->  (∀ w. w  -> Term' (v :▹ w) ) -> Primop v 
splicePrim (Abs' e) e2 = Abs' (spliceAbs e e2)
--splicePrim Tru' e2 = Tru'
--splicePrim Fals' e2 = Fals'
splicePrim (Var' v) e2 = Var' v
splicePrim (y :- y') e2 = y :- y'
splicePrim (Π1 y) e2 = Π1 y
splicePrim (Π2 y) e2 = Π2 y  

var' :: forall a b. (a :∈ b) => a → Primop b
var' = Var' . lk

cps :: Term v -> Term' v
-- cps Tru = Let Tru' (Halt' . There)
-- cps Fals = Let Fals' (Halt' . There) 
cps (Var v) = Halt' v
cps (App e1 e2) = splice (cps e1) $ \ f -> 
                      splice (wk (cps e2)) $ \ x →
                      Let (Abs' (\x -> Halt' (lk x))) $ \k →
                      Let (lk x :- lk k)    $ \p ->
                      App' (lk f) (lk p)
                      
cps (Lam _ e') =  Let (Abs' $ \p -> Let (Π1 (lk  p)) $ \x -> 
                                    Let (Π2 (lk p)) $ \k ->
                                    splice (wk (cps (e' x))) $ \r -> 
                                    App' (lk k) (lk r))
                      (\x -> Halt' (lk x))
                 
todo = error "todo!"                 
                  


class x :∈ γ where
  lk :: x -> γ
  
instance x :∈ (γ :▹ x) where
  lk = Here
  
instance (x :∈ γ) => x :∈ (γ :▹ y) where
  lk = There . lk


class a :< b where
  inj :: a → b

instance a :< a where inj = id

instance Zero :< a where inj = magic

instance (γ :< δ) => (γ :▹ v) :< (δ :▹ v) where  inj = mapu inj id

instance (a :< c) => a :< (c :▹ b) where
  inj = There . inj

instance Functor ((:▹) a) where
  fmap _ (There x) = There x
  fmap f (Here x) = Here (f x)

testMe = freeVars ((Lam (Name "x") (\x -> App (var x) (var 'c'))) :: Term (a :▹ Char))
       
-- -}
-- -}
-- -}
-- -}
-- -}

