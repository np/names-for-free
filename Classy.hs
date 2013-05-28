{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, Rank2Types,
             EmptyDataDecls, PatternGuards,
             UnicodeSyntax, TypeOperators, GADTs, OverlappingInstances,
             UndecidableInstances, IncoherentInstances, OverloadedStrings, StandaloneDeriving, KindSignatures, RankNTypes, ScopedTypeVariables, TypeFamilies, ViewPatterns #-}
module Classy where

import Prelude hiding (sequence,elem)
import Data.String
import Data.List (nub,elemIndex)
import Data.Maybe (fromJust)
import Control.Monad (join)
import Data.Functor
import Control.Applicative
import Data.Traversable
import Data.Foldable
import Data.Monoid

--------------------------------
-- Generic programming prelude

type (∪) a b = (:▹) a b

data (:▹) a b = There a | Here b 
data Zero

elim :: (γ -> a) -> (v -> a) -> γ :▹ v -> a
elim f _ (There x) = f x
elim _ g (Here x) = g x
  
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
   

var :: Monad m => forall a γ. (a :∈ γ) => a → m γ
var = return . lk

lam :: Name → (forall w. w → Term (v ∪ w)) → Term v
lam = Lam

-- A closed term can be given the 'Term Zero' type.
-- More generally any type can be used as the type
-- of the free variables of a closed term including
-- a polymorphic type.
idZero :: Term Zero
idZero = lam "x" (\x → var x)


-- fmap magic, wk...

id' :: Term a
id' = lam "x" (\x → var x)

const' :: Term a
const' = lam "x" (\x → lam "y" (\_y → var x))

testfv :: Term String
testfv = Var "x1" `App` Lam "x2" (\x2->
           Var (There "x3") `App` var x2)

(@@) :: Term a -> Term a -> Term a
(@@) = app

-- oops' = lam "x" (\x → lam "y" (\y → Var (Here x)))

---------------------
-- Display code

instance Show x => Show (Term x) where
  show = disp

-- half broken since names are never freshen
disp :: Show x => Term x → String
disp (Var x)    = show x
disp (App a b)  = "(" ++ disp a ++ ")" ++ disp b
disp (Lam nm f) = "λ" ++ unName nm ++ "." ++ disp (f nm)

data Disp a = Disp { dispVar :: a -> String
                   , curDispId :: Int }

extDisp :: Name -> Disp a -> Disp (a ∪ w)
extDisp nm (Disp v n) = Disp v' (n+1) where
  v' (There a) = v a
  v' (Here _) = show (mkName nm n)

mkName :: Name -> Int -> Name
mkName (Name nm) i = Name $ nm ++ show i

--dispVar :: Disp a -> Term a → ShowS

text :: String -> ShowS
text s1 s2 = s1 ++ s2

disp' :: Disp a -> Term a → ShowS
disp' d (Var x)    = text (dispVar d x)
disp' d (App a b)  = text "(" . disp' d a . text ")" . disp' d b
disp' d (Lam nm f) = text "λ" . text (show nm') . text "." . disp' d' (f ())
  where d'  = extDisp nm d
        nm' = mkName nm (curDispId d)

dispZero :: Term Zero -> String
dispZero t = disp' (Disp magic 0) t ""

printZero :: Term Zero -> IO ()
printZero = putStrLn . dispZero

---------------------
-- Catamorphism

cata :: (b -> a) -> ((a -> a) -> a) -> (a -> a -> a) -> Term b -> a
cata fv _  _  (Var x)   = fv x
cata fv fl fa (App f a) = fa (cata fv fl fa f) (cata fv fl fa a)
cata fv fl fa (Lam _ f) = fl (cata (extend fv) fl fa . f)

extend :: (a -> b) -> (a :▹ b) -> b
extend g = elim g id

cata' :: (b -> a) -> ((a -> a) -> a) -> (a -> a -> a) -> Term b -> a
cata' fv _  _  (Var x)   = fv x
cata' fv fl fa (App f a) = fa (cata fv fl fa f) (cata fv fl fa a)
cata' fv fl fa (Lam _ f) = unpack f $ \x t -> fl $ \xv -> (cata (extend' fv x xv) fl fa t)

extend' :: (a -> b) -> v -> b -> (a :▹ v) -> b
extend' g _ k = elim g (const k)


-----------------------------------------------------------
-- Terms are monads
-- (which means they support substitution as they should)

wk :: (Functor f, γ :< δ) => f γ -> f δ
wk = fmap inj

-- Kleisli arrows arising from the Term monad
type Kl m v w = v → m w

-- Union is a functor in the category of Kleisli arrows
lift :: (Functor f, Monad f) => Kl f v w → Kl f (v :▹ x) (w :▹ x)
lift θ (There x) = wk (θ x)
lift _ (Here x) = var x


{-
instance Monad Term where
  Var x    >>= θ = θ x
  Lam nm t >>= θ = Lam nm (\x → t x >>= lift θ)
  App t u  >>= θ = App (t >>= θ) (u >>= θ)

  return = Var
-}

-- In this instance one pays the cost in the packing.  But it could
-- potentially be optimised away in the '▹ ()' implementation since
-- the underlying (dynamic) fmap is from () to ().
instance Monad Term where
  Var x    >>= θ = θ x
  Lam nm f >>= θ = unpack f $ \x t -> lam'' nm x (t >>= lift θ)
  App t u  >>= θ = App (t >>= θ) (u >>= θ)

  return = Var


subst :: Monad m => (v → m w) → m v → m w
subst = (=<<)


-- As with any monad, fmap can be derived from bind and return.
-- This is a bit nasty here though. Indeed the definition of bind
-- uses lift which uses wk which uses fmap.
-- instance Functor Term where
--  fmap f t = t >>= return . f

instance Functor Term where
  fmap f (Var x) = Var (f x)
  fmap f (Lam nm g) = Lam nm (\x -> fmap (mapu f id) (g x))
  fmap f (App t u) = App (fmap f t) (fmap f u)

-- Substitute in an open term
subst' :: (∀v. v → Term v) → Term w → Term w
subst' t u = join (t u)


-- Nbe (HOAS-style)
eval :: Term v -> Term v
eval (Var x) = Var x
eval (Lam n t) = Lam n (eval . t)
eval (App t u) = app (eval t) (eval u)

app :: Term a -> Term a -> Term a
app (Lam _ t) u = subst0 =<< t u -- FIXME: should use hereditary subst.
app t u = App t u

subst0 :: Monad tm => v :▹ tm v -> tm v
subst0 (Here x) = x
subst0 (There x) = return x

{-
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

sizeM :: Term Int -> Int
sizeM (Var x) = x
sizeM (Lam _ g) = 1 + sizeM (fmap untag (g 1))
sizeM (App t u) = 1 + sizeM t + sizeM u


{-
sizeFO :: Term a -> Int
sizeFO (Var _) = 1
sizeFO (Lam _ g) = 1 + sizeFO (g ())
sizeFO (App t u) = 1 + sizeFO t + sizeFO u
 
sizeSafe :: Term a -> Int
sizeSafe (Var _) = 1
sizeSafe (Lam _ g) = unpack g $ \ _ t -> 1 + sizeSafe t
sizeSafe (App t u) = 1 + sizeSafe t + sizeSafe u
-}


sizeSafeEnv :: (a -> Int) -> Term a -> Int
sizeSafeEnv f (Var x) = f x
sizeSafeEnv f (Lam _ g) = unpack g $ \ x t -> 
    1 + sizeSafeEnv (extend' f x 1) t

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


-----------------------------
-- Pack/Unpack

type Binding f a = forall v. v -> f (a :▹ v)

data DualBinding f a where
  D :: v -> f (a :▹ v) -> DualBinding f a

unpack_ :: Binding f a -> DualBinding f a 
unpack_ f = D () (f ())

pack_ :: Functor f => DualBinding f a -> Binding f a
pack_ (D _ t) x = fmap (mapu id (const x)) t

-- pack :: (Functor f,v ∈ a) => v -> f a -> Binding (Diff a v) a
pack :: Functor f => v -> f (a :▹ v) -> Binding f a
pack _ t x = fmap (mapu id (const x)) t

-- Generalisation
pack' :: forall f v a b w. (Functor f, Insert v a b) => v -> f b -> (w -> f (a :▹ w))
pack' _ t x = fmap (shuffle cx) t
  where cx :: v -> w
        cx _ = x


unpack :: (forall v. v → f (w :▹ v)) -> (forall v. v -> f (w :▹ v) -> a) -> a
unpack b k = k () (b ())

unpack2 :: (forall v. v → f (w :▹ v)) -> 
           (forall v. v → g (w :▹ v)) -> 
             
           (forall v. v → f (w :▹ v) -> 
                          g (w :▹ v) -> a) ->
           a 
unpack2 f f' k = k () (f ()) (f' ())          

cmpTerm' :: Cmp a b -> Cmp (Term a) (Term b)
cmpTerm' cmp (Var x1) (Var x2) = cmp x1 x2
cmpTerm' cmp (App t1 u1) (App t2 u2) =
  cmpTerm' cmp t1 t2 && cmpTerm' cmp u1 u2
cmpTerm' cmp (Lam _ f1) (Lam _ f2) =
  unpack f1 $ \x1 t1 ->
  unpack f2 $ \x2 t2 ->
  cmpTerm' (extendCmp' x1 x2 cmp) t1 t2
cmpTerm' _ _ _ = False

-- The two first arguments are ignored and thus only there
-- to help the user not make a mistake about a' and b'.
extendCmp' :: a' -> b' -> Cmp a b -> Cmp (a ∪ a') (b ∪ b')
extendCmp' _ _ f (There x) (There y)  = f x y
extendCmp' _ _ _ (Here _)  (Here _)   = True
extendCmp' _ _ _ _         _          = False

instance Eq w => Eq (w :▹ v) where
  Here _ == Here _ = True
  There x == There y = x == y
  _ == _ = False

  
memberOf :: Eq w => w -> Term w -> Bool
memberOf x t = x `elem` freeVars t

occursIn :: (Eq w, v :∈ w) => v -> Term w -> Bool
occursIn x t = lk x `elem` freeVars t

isOccurenceOf :: (Eq w, v :∈ w) => w -> v -> Bool
isOccurenceOf x y = x == lk y

rm :: [v :▹ a] -> [v]
rm xs = [x | There x <- xs]

freeVars :: Term w -> [w]
freeVars (Var x) = [x]
freeVars (Lam _ f) = unpack f $ \_ t -> rm $ freeVars t
freeVars (App f a) = freeVars f ++ freeVars a

canEta :: Term Zero -> Bool
canEta (Lam _ e) = case unpack_ e of
  D x (App e1 (Var y)) -> lk x == y && not (lk x `memberOf` e1)
  _ -> False
canEta _ = False


-- recognizer of \x -> \y -> f x
recognize :: Term Zero -> Bool
recognize t0 = case t0 of 
    Lam _ f -> unpack f $ \x t1 -> case t1 of
      Lam _ g -> unpack g $ \_y t2 -> case t2 of
        (App func (Var arg)) -> arg == lk x && not (lk x `memberOf` func)
        _ -> False   
      _ -> False   
    _ -> False   

-- recognizer of \x -> \y -> f x
recognize' :: Term Zero -> Bool
recognize' (Lam _ (unpack_ -> D x (Lam _ (unpack_ -> D _ (App func (Var arg))))))
     = arg == lk x && not (lk x `memberOf` func)
recognize' _ = False        

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
  
instance Functor Primop where  
  fmap f (Π1 x) = Π1 (f x)
instance Functor Term' where 
  fmap f (Halt' x) = Halt' (f x)
  fmap f (App' x y) = App' (f x) (f y)
  fmap f (Let p g) = Let (fmap f p) (\x -> fmap (mapu f id) (g x))
  
  
(>>==) :: Primop a -> (a -> Term' b) -> Primop b
Abs' g >>== θ = Abs' (\x -> g x  >>= lift θ)
-- ...
-- FIXME: JP: I do not see how to write the other cases
          
instance Monad Term' where  
  return = Halt'
  
  Halt' x >>= θ = θ x
  Let t g >>= θ = Let (t >>== θ) (\x -> g x >>= lift θ)
  App' t u >>= θ = appCps (θ t) (θ u)
  -- The App case does not seem to do the same as splice.

appCps :: Term' a -> Term' a -> Term' a    
appCps t1 t2 = 
  splice t1 $ \ f -> 
  splice (wk t2) $ \ x →
  Let (Abs' (\y -> Halt' (lk y))) $ \k →
  Let (lk x :- lk k)    $ \p ->
  App' (lk f) (lk p)
  
  
spliceAbs :: ∀ v.
             (forall w. w  → Term' (v :▹ w) ) -> 
             (∀ w. w  → Term' (v :▹ w) ) -> 
             forall w. w  → Term' (v :▹ w) 
spliceAbs e' e2 x = splice (e' x) (\ x₁ → wk (e2 x₁))

splice' :: forall v  .
         Term' v  ->
         (∀ w. w  -> Term' (v :▹ w) ) -> 
         Term' v                                          
splice' t u = subst0 =<< u t

-- in e1, substitude Halt' by an arbitrary continuation e2
splice :: forall v  .
         Term' v  ->
         (∀ w. w  -> Term' (v :▹ w) ) -> 
         Term' v 
splice (Halt' v) e2 =  fmap untag (e2 v)
splice (App' f x)  _ = App' f x
splice (Let p e') e2 = Let (splicePrim p e2)  ( spliceAbs e' e2 )

splicePrim :: forall v. Primop v  ->  (∀ w. w  -> Term' (v :▹ w) ) -> Primop v 
splicePrim (Abs' e1) e2 = Abs' (spliceAbs e1 e2)
--splicePrim Tru'  _ = Tru'
--splicePrim Fals' _ = Fals'
splicePrim (Var' x) _ = Var' x
splicePrim (x :- y) _ = x :- y
splicePrim (Π1 x)   _ = Π1 x
splicePrim (Π2 x)   _ = Π2 x

cps :: Term v -> Term' v
-- cps Tru = Let Tru' (Halt' . There)
-- cps Fals = Let Fals' (Halt' . There) 
cps (Var v) = Halt' v
cps (App e1 e2) = splice (cps e1) $ \ f -> 
                      splice (wk (cps e2)) $ \ x →
                      Let (Abs' (\y -> Halt' (lk y))) $ \k →
                      Let (lk x :- lk k)    $ \p ->
                      App' (lk f) (lk p)
                      
cps (Lam _ e') =  Let (Abs' $ \p -> Let (Π1 (lk  p)) $ \x -> 
                                    Let (Π2 (lk p)) $ \k ->
                                    splice (wk (cps (e' x))) $ \r -> 
                                    App' (lk k) (lk r))
                      (\x -> Halt' (lk x))
                 
-----------------  
-- Traversable

mapu :: (u -> u') -> (v -> v') -> (u :▹ v) -> (u' :▹ v')
mapu f _ (There x) = There (f x)
mapu _ g (Here  x) = Here  (g x)

instance Foldable Term where
  foldMap = foldMapDefault

instance Traversable Term where
  traverse f (Var x) =
    Var <$> f x
  traverse f (App t u) =
    App <$> traverse f t <*> traverse f u
  traverse f (Lam nm b) = unpack b $ \x b' -> 
      lam'' nm x <$> traverse (traverseu f pure) b'

lam' :: Name → v -> Term (w :▹ v) → Term w
lam' nm x t = Lam nm (pack x t)

lam'' :: Insert v a b => Name → v -> Term b → Term a
lam'' nm x t = Lam nm (pack' x t)

traverseu :: Applicative f => (a -> f a') -> (b -> f b') ->
                              a ∪ b -> f (a' ∪ b')
traverseu f _ (There x) = There <$> f x
traverseu _ g (Here  x) = Here  <$> g x

fv' :: Term a -> [a]
fv' = toList

memberOf' :: Eq a => a -> Term a -> Bool
x `memberOf'` t = getAny $ foldMap (Any . (==x)) t

type Succ a = a ∪ ()

{-
instance Applicative ((∪) ()) where
  pure = Here
  Here f <*> Here x = Here (f x)
  _     <*> _     = There ()

instance Monad ((∪) ()) where
  return = Here
  Here x >>= f = f x
  There _ >>= _ = There ()
-}

-------------
-- α-eq

type Cmp a b = a -> b -> Bool

succCmp :: Cmp a b -> Cmp (Succ a) (Succ b)
succCmp f (There x)  (There y)  = f x y
succCmp _ (Here ()) (Here ()) = True
succCmp _ _        _        = False

cmpTerm :: Cmp a b -> Cmp (Term a) (Term b)
cmpTerm cmp (Var x1) (Var x2) = cmp x1 x2
cmpTerm cmp (App t1 u1) (App t2 u2) =
  cmpTerm cmp t1 t2 && cmpTerm cmp u1 u2
cmpTerm cmp (Lam _ f1) (Lam _ f2) =
  cmpTerm (succCmp cmp) (f1 ()) (f2 ())
cmpTerm _ _ _ = False




instance Eq a => Eq (Term a) where
  -- (==) = cmpTerm (==)
  Var x == Var x' = x == x'
  Lam _ g == Lam _ g' = unpack2 g g' $ \_ t t' -> t == t'
  App t u == App t' u' = t == t' && u == u'        



close :: Traversable tm => tm (Succ a) -> Maybe (tm a)
close = traverse succToMaybe


closeAll :: Traversable tm => tm a -> Maybe (tm Zero)
closeAll = traverse (const Nothing)


succToMaybe :: Succ a -> Maybe a
succToMaybe (There a) = Just a
succToMaybe (Here _) = Nothing

canη' :: Eq a => Term a -> Bool
canη' (Lam _ t)
  | App u (Var (Here ())) <- t ()
    = not (Here () `memberOf` u)
canη' _ = False

ηred :: Term a -> Term a
ηred (Lam _ t)
  | App u (Var (Here ())) <- t ()
  , Just u' <- close u
  = u'
ηred t = t

ηexp :: Term a -> Term a
ηexp t = Lam "x" $ \x-> App (wk t) (var x)

class Insert v a b where    
  shuffle :: (v -> w) -> b -> a :▹ w

instance Insert v a (a :▹ v) where
  shuffle = mapu id
  
instance Insert v a b => Insert v (a :▹ v') (b :▹ v') where
  shuffle _ (Here x)  = There (Here x)
  shuffle f (There x) = mapu There id $ shuffle f x

class x :∈ γ where
  -- type Diff γ x -- GHC refuses overlapping type family instances!
  lk :: x -> γ
  
  
instance x :∈ (γ :▹ x) where
  -- type Diff (γ :▹ x) x  = γ
  lk = Here

instance (x :∈ γ) => x :∈ (γ :▹ y) where
  -- type Diff (γ :▹ y) x = Diff γ x :▹ y 
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

testMe :: [a :▹ Char]
testMe = freeVars (Lam (Name "x") (\x -> App (var x) (var 'c')))
       
         
-----------------------------
-- Krivine Abstract Machine
-- (A call-by-name lambda-calculus abstract machine, sec. 1)

data Env w' w where -- input (w) and output (w') contexts
  Cons :: v -> Closure w -> Env w' w -> Env (w' :▹ v) w
  Nil :: Env w w 
  
look :: w' -> Env w' w -> Closure w
look = undefined
  
data Closure w where
  C :: Term w' -> Env w' w -> Closure w
  
type Stack w = [Closure w]  
  
kam :: Closure w -> Stack w -> Maybe (Closure w,Stack w)
kam (C (Lam _ f) ρ) (u:s) = unpack f $ \ x t -> Just (C t (Cons x u ρ), s)
kam (C (App t u) ρ) s    = Just (C t ρ,C u ρ:s)
kam (C (Var x)   ρ) s    = Just (look x ρ, s)
kam _ _ = Nothing

-------------------
-- Closure conversion 
-- following Guillemette&Monnier, A Type-Preserving Closure Conversion in Haskell, fig 2.

instance Functor LC where
  fmap f t = t >>= return . f

instance Monad LC where
  return = VarC
  VarC x >>= θ = θ x
  Closure c env >>= θ = Closure c (env >>= θ)
  LetOpen t g >>= θ = LetOpen (t >>= θ) (\f env -> g f env >>= lift (lift θ))
  Tuple ts >>= θ = Tuple (map (>>= θ) ts)
  Index t i >>= θ = Index (t >>= θ) i
  AppC t u >>= θ = AppC (t >>= θ) (u >>= θ)
  
data LC w where
  VarC :: w -> LC w
  Closure :: (forall vx venv. vx -> venv -> LC (Zero :▹ venv :▹ vx)) -> -- ^ code
             LC w -> -- ^ env
             LC w
  LetOpen :: LC w -> (forall vf venv. vf -> venv -> LC (w :▹ vf :▹ venv)) -> LC w
  Tuple :: [LC w] -> LC w
  Index :: LC w -> Int -> LC w
  AppC :: LC w -> LC w -> LC w
 
cc :: forall w. Eq w => Term w -> LC w  
cc (Var x) = VarC x
cc (Lam _ f) = unpack f $ \_x e ->
  let yn = nub $ rm $ freeVars e 
      
  in Closure (\x' env -> subst (\z -> case z of
                                             Here _ -> var x' -- x becomes x'
                                             There w -> fmap There (Index (var env) (fromJust $ elemIndex w yn))
                                                        -- other free vars are looked up in the env.
                                             -- unfortunately wk fails here.
                                         ) (cc e)) 
             (Tuple $ map VarC yn)
cc (App e1 e2) = LetOpen (cc e1) (\xf xenv -> (var xf `AppC` wk (cc e2)) `AppC` var xenv)

-- Possibly nicer version.
cc' :: forall w. Eq w => Term w -> LC w  
cc' (Var x) = VarC x
cc' t0@(Lam _ f) = 
  let yn = nub $ freeVars t0
  in Closure (\x env -> subst (lift (\w -> (Index (var env) (fromJust $ elemIndex w yn))))
                                           (cc' (f x)))
             (Tuple $ map VarC yn)
cc' (App e1 e2) = LetOpen (cc' e1) (\xf xenv -> (var xf `AppC` wk (cc' e2)) `AppC` var xenv)


-----------------------
-- 


-- -}
-- -}
-- -}
-- -}
-- -}

