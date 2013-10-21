-- Extracted from:
--   “Proving Correctness of Compilers using Structured Graphs”
--   by Patrick Bahr
--   at http://diku.dk/~paba/graphs.tgz
-- Extended to use Bound + our polymorphic views

{-# LANGUAGE DeriveFunctor, FlexibleContexts, RankNTypes, 
  GeneralizedNewtypeDeriving, DeriveFoldable, DeriveTraversable,
  StandaloneDeriving, DataKinds, GADTs, KindSignatures, ScopedTypeVariables,
  MultiParamTypeClasses, FunctionalDependencies,
  UndecidableInstances, FlexibleInstances #-} -- only needed for pretty printing

import Prelude hiding (sequence)
import Control.Monad.State hiding (sequence, foldM)
import Data.Traversable
import Data.Foldable hiding (fold)

import Bound
import Bound.Var
import Bound.Var.Injections
--import Data.Bifunctor
import Data.Void

import Prelude.Extras

type Succ = Var ()

data Expr  =  Val Int  |  Add    Expr Expr
           |  Throw    |  Catch  Expr Expr
deriving instance Show Expr

ex0 :: Expr
ex0 = Val 3 `Add` (Catch (Val 4 `Add` Throw) (Val 5))

ex1 :: Expr
ex1 = Val 3 `Add` (Catch (Val 4 `Add` Throw) (Val 0) `Add` Val 5)

ex2 :: Expr
ex2 = (Val 2 `Catch` Val 3) `Add` Val 4

ex3 :: Expr
ex3 = (Throw `Catch` Val 3) `Add` Val 4

eval :: Expr -> Maybe Int
eval (  Val n)      =  Just n
eval (  Add x y)    =  case eval x of
                         Nothing  ->  Nothing
                         Just n   ->  case eval y of
                                       Nothing  -> Nothing
                                       Just m   -> Just (n+m)
eval    Throw       =  Nothing
eval (  Catch x h)  =  case eval x of
                         Nothing  -> eval h
                         Just n   -> Just n


data Code_  =  PUSH_ Int Code_  | ADD_ Code_         | HALT_
            |  UNMARK_ Code_    | MARK_ Code_ Code_  | THROW_
deriving instance Show Code_
deriving instance Eq Code_

{-
compA :: Expr -> Code_ -> Code_
compA (Val n)      c   = PUSH_ n c
compA (Add x y)    c   = compA x (compA y (ADD_ c))
compA Throw        _c  = THROW_
compA (Catch x h)  c   = MARK_ (compA h c) (compA x (UNMARK_ c))
-}
infixr 0  |>
(|>) :: (a -> b) -> a -> b
f |> x = f x
{-
comp :: Expr -> Code_
comp e = compA e |> HALT_
-}
type Stack  =  [Item]
data Item   =  VAL Int | HAN (Stack -> Stack)
{-
exec :: Code_ -> Stack -> Stack
exec (PUSH_ n c)  s = exec c (VAL n : s)
exec (ADD_ c)     s =  case s of 
                          (VAL m : VAL n : s') -> exec c (VAL (n+m) : s')
exec THROW_       s = unwind s
exec (MARK_ h c)  s = exec c (HAN (exec h) : s)
exec (UNMARK_ c)  s =  case s of 
                          (x : HAN _ : s') -> exec c (x:s')
exec HALT_        s = s
-}

unwind :: Stack -> Stack
unwind []           =  []
unwind (VAL _ : s)  =  unwind s
unwind (HAN h : s)  =  h s
{-
conv (Just n)  = [Val n]
conv Nothing   = []
-}

data Tree f = In (f (Tree f))

data Code a  =  PUSH Int a  | ADD a     | HALT
             |  MARK a a    | UNMARK a  | THROW
              deriving (Show, Functor,Foldable,Traversable)
deriving instance Show (f (Tree f)) => Show (Tree f)
instance Show1 Code where showsPrec1 = showsPrec

code_Alg :: Code Code_ -> Code_
code_Alg (PUSH i c) = PUSH_ i c
code_Alg (ADD c)    = ADD_ c
code_Alg HALT       = HALT_
code_Alg (MARK h c) = MARK_ h c
code_Alg (UNMARK c) = UNMARK_ c
code_Alg THROW      = THROW_

sizeCode :: Num n => Code n -> n
sizeCode (PUSH _ x) = 1 + x
sizeCode (ADD x)    = 1 + x
sizeCode HALT       = 1
sizeCode (MARK x y) = 1 + x + y
sizeCode (UNMARK x) = 1 + x
sizeCode THROW      = 1

fromTreeCode :: Tree Code -> Code_
fromTreeCode = fold code_Alg

compAT :: Expr -> Tree Code -> Tree Code
compAT (  Val n)       c   =  iPUSH n |> c
compAT (  Add x y)     c   =  compAT x |> compAT y |> iADD |> c
compAT    Throw        _c  =  iTHROW
compAT (  Catch x h)   c   =  iMARK (compAT h |> c) |> compAT x |> iUNMARK |> c

compT :: Expr -> Tree Code
compT e = compAT e |> iHALT

class Wrap f a where
  wrap :: f a -> a

instance Wrap f (Tree f) where wrap = In

iPUSH :: Wrap Code a => Int -> a -> a
iPUSH i c = wrap $ PUSH i c

iADD :: Wrap Code a => a -> a
iADD c = wrap $ ADD c

iTHROW :: Wrap Code a => a
iTHROW = wrap THROW

iMARK :: Wrap Code a => a -> a -> a
iMARK h c = wrap (MARK h c)

iUNMARK :: Wrap Code a => a -> a
iUNMARK c = wrap (UNMARK c)

iHALT :: Wrap Code a => a
iHALT = wrap HALT

fold :: Functor f => (f r -> r) -> Tree f -> r
fold alg (In t)     = alg (fmap (fold alg) t)

execAlg :: Code (Stack -> Stack) -> Stack -> Stack
execAlg (PUSH n c)  s = c (VAL n : s)
execAlg (ADD c)     s =  case s of 
                           (VAL m : VAL n : s') -> c (VAL (n+m) : s')
                           _ -> error "bad stack"
execAlg THROW       s = unwind s
execAlg (MARK h c)  s = c (HAN h : s)
execAlg (UNMARK c)  s =  case s of 
                           (x : HAN _ : s') -> c (x:s')
                           _ -> error "bad stack"
execAlg HALT        s = s

execT :: Tree Code -> Stack -> Stack
execT = fold execAlg

runS :: (Stack -> Stack) -> Maybe Int
runS f = case f [] of
           [VAL x] -> Just x
           _       -> Nothing

{-
data Graph' f v  =  GIn (f (Graph' f v))
                 |  Let (Graph' f v) (v -> Graph' f v)
                 |  Var v

newtype Graph f = Graph {unGraph :: forall v . Graph' f v}

gPUSH :: Int -> Graph' Code v -> Graph' Code v
gPUSH i c = GIn (PUSH i c)
gADD c = GIn (ADD c)
gTHROW = GIn THROW
gMARK h c = GIn (MARK h c)
gUNMARK c = GIn (UNMARK c)
gHALT     = GIn HALT

compAG_             :: Expr -> Graph' Code a -> Graph' Code a
compAG_ (Val n)      c   =  gPUSH n |> c
compAG_ (Add x y)    c   =  compAG_ x |> compAG_ y |> gADD |> c
compAG_ (Throw)      _c  =  gTHROW
compAG_ (Catch x h)  c   =  gMARK (compAG_ h |> c) |> compAG_ x |> gUNMARK |> c

compAG :: Expr -> Graph' Code a -> Graph' Code a
compAG (Val n)      c   =  gPUSH n |> c
compAG (Add x y)    c   =  compAG x |> compAG y |> gADD |> c
compAG (Throw)      _c  =  gTHROW
compAG (Catch x h)  c   =  Let c (\c' ->  gMARK (compAG h |> Var c')
                                         |> compAG x |> gUNMARK |> Var c')

compG :: Expr -> Graph Code
compG e = Graph (compAG e |> gHALT)

gfold :: Functor f => (v -> r) -> (r -> (v -> r) -> r) -> (f r -> r)
      -> Graph f -> r
gfold v l i (Graph g) = trans g where
    trans (Var x)     = v x
    trans (Let e f)   = l (trans e) (trans  . f)
    trans (GIn t)     = i (fmap trans t)

ufold :: Functor f => (f r -> r) -> Graph f -> r
ufold = gfold id (\ e f -> f e)

execG :: Graph Code -> Stack -> Stack
execG = ufold execAlg

unravel :: Functor f => Graph f -> Tree f
unravel = ufold In

unravel_ :: Functor f => Graph f -> Tree f
unravel_ (Graph g) = unravel' g

unravel' :: Functor f => Graph' f (Tree f) -> Tree f
unravel' (Var x)      = x
unravel' (Let e f)    = unravel'  (f (unravel' e))
unravel' (GIn t)      = In (fmap unravel' t)

-- Fin

data Nat = O | S Nat

data Fin :: Nat -> * where
   F1 :: Fin (S n)
   FS :: Fin n -> Fin (S n)

(!) :: Vector n a -> Fin n -> a
(Cons x _) ! F1 = x
(Cons _ xs) ! (FS f) = xs ! f
Nil ! _ = error "not gonna happen"

data GraphB' :: Nat -> (* -> *) -> * {-"\,"-} where
  GInB   :: f (GraphB' n f)                 -> GraphB' n f
  VarB   :: Fin n                           -> GraphB' n f
  LetB   :: GraphB' n f -> GraphB' (S n) f  -> GraphB' n f

type GraphB = GraphB' O

data Vector :: Nat -> * -> * {-"\,"-} where
   Nil   ::                     Vector  O      a
   Cons  :: a -> Vector n a ->  Vector  (S n)  a

gfoldB' :: forall c f v n . Functor f  =>  (v -> c) -> (c -> (v -> c) -> c) -> (f c -> c)
                                       ->  GraphB' n f -> Vector n v -> c
gfoldB' v l i g args = trans args g where 
        trans :: forall n . Vector n v -> GraphB' n f -> c
        trans args (VarB x)    = v (args ! x)
        trans args (LetB e f)  = l (trans args e) (\ x -> trans (x `Cons` args) f)
        trans args (GInB t)    = i (fmap (trans args) t)

gfoldB :: Functor f  =>  (v -> c) -> (c -> (v -> c) -> c) -> (f c -> c)
                     ->  GraphB f -> c
gfoldB v l i g = gfoldB' v l i g Nil

ufoldB' :: Functor f => (f c -> c) -> GraphB' n f -> Vector n c -> c
ufoldB' = gfoldB' id (\ e f -> f e)

unravelB' :: Functor f => GraphB' n f -> Vector n (Tree f) -> Tree f
unravelB' = ufoldB' In

ufoldB :: Functor f => (f c -> c) -> GraphB f -> c
ufoldB alg g = ufoldB' alg g Nil

unravelB :: Functor f => GraphB f -> Tree f
unravelB g = unravelB' g Nil

-- Linear code

type Label  =  Int

data Inst   =  IPUSH Int | IADD | ITHROW | IMARK Label 
            |  IUNMARK | JUMP Label | LABEL Label

type CodeL  =  [Inst]

deriving instance Eq Inst
deriving instance Show Inst

runFresh :: Fresh a -> a
runFresh (Fresh m) = fst (runState m 0)

fresh :: Fresh Label
fresh = Fresh (do l <- get; put (l+1); return l)
newtype Fresh a = Fresh (State Label a) deriving Monad

linearCode :: Graph Code -> CodeL
linearCode c = runFresh (gfold lVar lLet lAlg c [])

(<:>) :: Monad m => a -> m [a] -> m [a]
ins <:> mc = mc >>= (\c -> return (ins : c))

lAlg :: Code (CodeL -> Fresh CodeL) -> CodeL -> Fresh CodeL
lAlg (ADD c)     d   = IADD <:> c d
lAlg (PUSH n c)  d   = IPUSH n <:> c d
lAlg THROW       _d  = return [ITHROW]
lAlg (MARK h c)  d   = fresh >>= \ l -> IMARK l <:> (c =<< LABEL l <:> h d)
lAlg (UNMARK c)  d   = IUNMARK <:> c d
lAlg HALT        _d  = return []

lVar :: Label -> CodeL -> Fresh CodeL
lVar l (LABEL l' : d) | l == l'  = return (LABEL l' : d)
lVar l d                         = return (JUMP l : d)

lLet :: (CodeL -> Fresh CodeL)  -> (Label -> CodeL -> Fresh CodeL) 
                                -> CodeL -> Fresh CodeL
lLet b s d = fresh >>= \l -> s l =<< LABEL l <:> b d

compL :: Expr -> CodeL
compL = linearCode . compG
-}

data TreeM f a = Return a | InM (f (TreeM f a))
deriving instance (Show (f (TreeM f a)), Show a) => Show (TreeM f a)

gfoldTM :: Functor f => (a -> r) -> (f r -> r) -> TreeM f a -> r
gfoldTM r _i (Return x) = r x
gfoldTM r  i (InM t)    = i (fmap (gfoldTM r i) t)

fromTreeMCode :: TreeM Code Void -> Code_
fromTreeMCode = gfoldTM absurd code_Alg

sizeT :: (Functor f, Num n) => (f n -> n) -> TreeM f v -> n
sizeT = gfoldTM (const 1)

instance Functor f => Functor (TreeM f) where
    fmap f (Return x) = Return (f x)
    fmap f (InM t)    = InM ((fmap . fmap) f t)

instance Functor f => Monad (TreeM f) where
    return          = Return
    Return x >>= f  = f x
    InM t    >>= f  = InM (fmap (\ s -> s >>= f) t)

instance Wrap f (TreeM f a) where wrap = InM

compAM :: Expr -> TreeM Code Void -> TreeM Code Void
compAM (  Val n)       c   =  iPUSH n c
compAM (  Add x y)     c   =  compAM x (compAM y (iADD c))
compAM    Throw        _c  =  iTHROW
compAM (  Catch x h)   c   =  iMARK (compAM h c) (compAM x (iUNMARK c))

hole :: Monad f => f ()
hole = return ()

data GraphN f a  = GInN (f (GraphN f a))
                 | LetN (GraphN f a) (Scope () (GraphN f) a)
                 | VarN a

instance Wrap f (GraphN f a) where wrap = GInN

instance Functor f => Functor (GraphN f) where
  fmap = liftM

instance Functor f => Monad (GraphN f) where
  return = VarN

  VarN x   >>= s = s x
  LetN e f >>= s = LetN (e >>= s) (f >>>= s)
  GInN t   >>= s = GInN (fmap (>>= s) t)

letN :: Functor f => GraphN f a -> (forall v. v -> GraphN f (Var v a)) -> GraphN f a
letN t f = LetN t (toScope $ f ())

unpackN :: Functor f => Scope () (GraphN f) a -> (forall v. v -> GraphN f (Var v a) -> r) -> r
unpackN g k = k () (fromScope g)

compN' :: Expr -> GraphN Code ()
compN' (Val n)     = iPUSH n hole
compN' (Add x y)   = compN' x >> compN' y >> iADD hole
compN' (Throw)     = iTHROW
compN' (Catch x h) = letN hole (\e -> iMARK
                        (compN' h >> var e)
                        (compN' x >> iUNMARK (var e)))

compN :: Expr -> GraphN Code Void
compN e = compN' e >> iHALT

gfoldN :: Functor f => (v -> r) -> (r -> (r -> r) -> r) -> (f r -> r)
      -> GraphN f v -> r
gfoldN v _ _ (VarN x)   = v x
gfoldN v l i (LetN e f) = unpackN f $ \x t -> l (gfoldN v l i e) (\y -> gfoldN (extend' v x y) l i t)
gfoldN v l i (GInN t)   = i (fmap (gfoldN v l i) t)

sizeN :: (Functor f, Num n) => (f n -> n) -> GraphN f v -> n
sizeN = gfoldN (const 1) (\x y -> 1 + x + y 0)

extend' :: (a -> b) -> v -> b -> (Var v a) -> b
extend' g _ k = unvar (const k) g

ufoldN :: Functor f => (f r -> r) -> GraphN f Void -> r
ufoldN alg = gfoldN absurd (\e f -> f e) alg

execGN :: GraphN Code Void -> Stack -> Stack
execGN = ufoldN execAlg

unravelN' :: Functor f => (a -> TreeM f b) -> GraphN f a -> TreeM f b
unravelN' f = gfoldN f (flip ($)) InM

unravelN :: Functor f => GraphN f a -> TreeM f a
unravelN = unravelN' return

{-
data GraphM' f b a  =  GReturn a
                    |  GInM (f (GraphM' f b a))
                    |  LetM (GraphM' f b a) (b -> GraphM' f b a)
                    |  VarM b

newtype GraphM f a = GraphM {unGraphM :: forall b . GraphM' f b a}

instance Functor f => Monad (GraphM' f b) where
  return x           = (GReturn x)

  VarM x      >>= _s  = VarM x
  LetM e f    >>= s   = LetM (e >>= s) (\ x -> f x >>= s) 
  GReturn x   >>= s   = s x
  GInM t      >>= s   = GInM (fmap (>>= s) t)

instance Functor f => Monad (GraphM f) where
    return x        = GraphM (return x)
    GraphM g >>= f  = GraphM (g >>= unGraphM . f)

gmPUSH i c = GInM (PUSH i c)
gmADD c    = GInM (ADD c)
gmTHROW    = GInM THROW
gmHALT     = GInM HALT
gmMARK h c = GInM (MARK h c)
gmUNMARK c = GInM (UNMARK c)

compCGM :: Expr -> GraphM' Code b ()
compCGM (Val n)     =  gmPUSH n hole
compCGM (Add x y)   =  compCGM x >> compCGM y >> gmADD hole
compCGM (Throw)     =  gmTHROW
compCGM (Catch x h) =  LetM hole (\e -> gmMARK 
                         (compCGM h >> VarM e) 
                         (compCGM x >> gmUNMARK (VarM e)))

compGM :: Expr -> GraphM Code Void
compGM e = GraphM (compCGM e >> gmHALT)

gfoldM :: Functor f => (v -> r) -> (r -> (v -> r) -> r) -> (f r -> r)
      -> GraphM f Void -> r
gfoldM v l i (GraphM g) = trans g where
    trans (VarM x)     = v x
    trans (LetM e f)   = l (trans e) (trans  . f)
    trans (GInM t)     = i (fmap trans t)
    trans (GReturn _)  = error "gfoldM on GReturn, not gonna happen"

ufoldM :: Functor f => (f r -> r) -> GraphM f Void -> r
ufoldM alg = gfoldM id (\ e f -> f e) alg

execGM :: GraphM Code Void -> Stack -> Stack
execGM = ufoldM execAlg

unravelM :: Functor f => GraphM f a -> TreeM f a
unravelM (GraphM g) = unravelM' g

unravelM' :: Functor f => GraphM' f (TreeM f a) a -> TreeM f a
unravelM' (VarM x)     = x
unravelM' (LetM e f)   = unravelM'  (f (unravelM' e))
unravelM' (GReturn x)  = Return x
unravelM' (GInM t)     = InM (fmap unravelM' t)

{-
instance (Functor f, Show (f StringP)) => Show (Tree f) where
    show (In t) = show (fmap (StringP . (++ ")") . ("(" ++) . show) t)

-- Pretty printing graphs
newtype StringP = StringP String
instance Show StringP where
    show (StringP s) = s

showGraph :: (Functor f, Show (f StringP)) => [String] -> Graph' f String -> String
showGraph _ (Var v) = "Var " ++ v
showGraph (n:ns) (Let e f) = "Let (" ++ showGraph ns e ++ ") (\\ " ++ n
                               ++ " -> " ++ showGraph ns (f n) ++ ")"
showGraph [] (Let _ _) = error "showGraph: out of fresh names"
showGraph ns (GIn t) = show (fmap (StringP . (++ ")") . ("(" ++) . showGraph ns) t)

instance (Functor f, Show (f StringP)) => Show (Graph f) where
    show (Graph g) = showGraph (map (\ i -> "v" ++ show i) [1..] ) g
    -}

-- -}
-- -}
-- -}
-- -}
-- -}

{-
{-# DEPRECATED h "h is undefined" #-}
h :: a
h = undefined "h"
data H = H
-}

text = (++)
parens prec f | prec <= 10 = text "(" . f . text ")"
              | otherwise  = f

atVar :: Functor f => Scope () f a -> v -> f (Var v a)
atVar t = undefined

atVar' :: Functor f => Scope () f a -> a -> f a
atVar' t = undefined

class (Functor f) => ShowS1 f where
  showsPrecMap1 :: Int -> (a -> ShowS) -> f a -> ShowS

showGraphN :: (Functor f, ShowS1 f) => [String] -> Int -> (a -> ShowS) -> GraphN f a -> ShowS
showGraphN _      prec shv (VarN v)   = shv v
showGraphN (n:ns) prec shv (LetN e f) = parens prec $
                                        text "let " . text n . text " = " . showGraphN ns 0 shv e . text " in "
                                      . showGraphN ns 0 (extend' shv undefined (text n)) (fromScope f)
                                      . text " end"
showGraphN [] _    _   (LetN _ _) = error "showGraphN: out of fresh names"
showGraphN ns prec shv (GInN t) = showsPrecMap1 prec (showGraphN ns 11 shv) t

instance (Functor f, ShowS1 f) => ShowS1 (GraphN f) where
    showsPrecMap1 prec f = showGraphN supply prec f
      where supply = ["x","y","z"] ++ map (\ i -> "v" ++ show i) [0..]

instance Show ShowS where
  showsPrec _ = id

instance ShowS1 Code where
  showsPrecMap1 prec f c = showsPrec prec $ fmap f c

instance Show a => Show (GraphN Code a) where
  showsPrec prec = showsPrecMap1 prec shows
