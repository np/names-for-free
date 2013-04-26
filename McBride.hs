
{-# LANGUAGE GADTs, DataKinds, OverlappingInstances, UndecidableInstances #-}

-- http://www.e-pig.org/epilogue/?p=773
-- a re-implementation by JP Bernardy

data Nat = Z | S Nat

data Fin :: Nat ->  * where             
  Fz :: Fin (S n)
  Fs :: Fin n -> Fin (S n)

data Term :: Nat -> * where             
  Var :: Fin n -> Term n
  Lam :: String -> Term (S n) -> Term n
  App :: Term n -> Term n -> Term n

class Leq (m :: Nat) (n :: Nat) where
    finj :: Fin m -> Fin n
    
instance Leq n n where
   finj = id
   
instance (o~S n,Leq m n) => Leq m o  where   
  finj = Fs . finj
  
cough :: (Fin (S m) -> Term m) -> Term m
cough f = f Fz

lam :: String -> ((forall n. (Leq (S m) n => Fin n)) -> Term (S m)) -> Term m
lam nm f = cough $ \fz -> Lam nm (f (finj fz))
  
id' = lam "x" $ \x -> lam "y" $ \y -> Var x `App` Var y  


-----------------
-- Display code

lk :: [a] -> Fin n -> a
lk (x:_) Fz = x
lk (_:xs) (Fs s) = lk xs s
  
disp :: [String] -> Term n -> String
disp xs (Var x) = lk xs x
disp xs (App a b) = "(" ++ disp xs a ++ ")" ++ disp xs b
disp xs (Lam nm f) = "λ" ++ nm ++ "." ++ disp (nm:xs) f

instance Show (Term n) where
  show = disp []
  