{-# LANGUAGE Rank2Types, OverloadedStrings, TypeOperators #-}
module TestPaperCode where

-- mostly based from bound sources and examples/Simple.hs

import Data.String
import Data.Foldable hiding (notElem, foldl)
import Data.Traversable
import Data.Functor
import Data.List (elemIndex,(!!))
import Data.Maybe (fromJust)
import Control.Monad hiding (mapM)
import System.Exit

import PaperCode hiding (($$), main)

type Scope b f a = f (a :▹ b)

abstract :: Functor f => (a -> Maybe b) -> f a -> Scope b f a
abstract f e = k <$> e where
  k y = case f y of
    Just z  -> New z
    Nothing -> Old y

-- | Abstract over a single variable
--
-- >>> abstract1 'x' "xyz"
-- Scope [B (),F "y",F "z"]
abstract1 :: (Functor f, Eq a) => a -> f a -> Scope () f a
abstract1 a = abstract (\b -> if a == b then Just () else Nothing)

-- | Enter a scope, instantiating all bound variables
--
-- >>> :m + Data.List
-- >>> instantiate (\x -> [toEnum (97 + x)]) $ abstract (`elemIndex` "bar") "barry"
-- "abccy"
instantiate :: Monad f => (b -> f a) -> Scope b f a -> f a
instantiate k e = e >>= \v -> case v of
  New b -> k b
  Old a -> return a

-- | Enter a 'Scope' that binds one variable, instantiating it
--
-- >>> instantiate1 "x" $ Scope [B (),F "y",F "z"]
-- "xyz"
instantiate1 :: Monad f => f a -> Scope n f a -> f a
instantiate1 e = instantiate (const e)

-- | A smart constructor for Lam
--
-- >>> lamE "y" (lamE "x" (V "x" :@ V "y"))
-- Lam (Scope (Lam (Scope (V (B ()) :@ V (F (V (B ())))))))
lamE :: Eq a => a -> Tm a -> Tm a
lamE v b = Lam (abstract1 v b)

-- | A smart constructor for let-bindings
-- notice that this is only syntactic sugar and that
-- the bindings are substituted away.

let_ :: (Foldable t, Monad t, Eq a) => [(a,t a)] -> t a -> t a
let_ [] b = b
let_ bs b = inst b where
  ns = map fst bs
  es = map (inst.snd) bs
  inst e = e >>= \x -> case elemIndex x ns of
    Just i  -> es !! i
    Nothing -> return x
infixr 0 !
(!) :: Eq a => a -> Tm a -> Tm a
(!) = lamE

-- | Lennart Augustsson's example from "The Lambda Calculus Cooked 4 Ways"
--
-- Modified to use recursive let, because we can.
--
-- >>> nf cooked == true
-- True

true :: Tm String
true = lamE "F" $ lamE "T" $ "T"

instance IsString a => IsString (Tm a) where
  fromString = Var . fromString

class App a where
  ($$) :: a -> a -> a
instance App (Tm a) where
  ($$) = App

cooked :: Int -> Tm a
cooked n = fromJust $ closed $ let_
  [ ("id",     "x" ! "x")
  , ("False",  "f" ! "t" ! "f")
  , ("True",   "f" ! "t" ! "t")
  , ("if",     "b" ! "t" ! "f" ! "b" $$ "f" $$ "t")
  , ("Zero",   "z" ! "s" ! "z")
  , ("Succ",   "n" ! "z" ! "s" ! "s" $$ "n")
  , ("one",    "Succ" $$ "Zero")
  , ("two",    "Succ" $$ "one")
  , ("three",  "Succ" $$ "two")
  , ("isZero", "n" ! "n" $$ "True" $$ ("m" ! "False"))
  , ("const",  "x" ! "y" ! "x")
  , ("Pair",   "a" ! "b" ! "p" ! "p" $$ "a" $$ "b")
  , ("fst",    "ab" ! "ab" $$ ("a" ! "b" ! "a"))
  , ("snd",    "ab" ! "ab" $$ ("a" ! "b" ! "b"))
  , ("fix",    "g" ! ("x" ! "g"$$ ("x"$$"x")) $$ ("x" ! "g"$$ ("x"$$"x")))
  , ("add",    "fix" $$ ("radd" ! "x" ! "y" ! "x" $$ "y" $$ ("n" ! "Succ" $$ ("radd" $$ "n" $$ "y"))))
  , ("mul",    "fix" $$ ("rmul" ! "x" ! "y" ! "x" $$ "Zero" $$ ("n" ! "add" $$ "y" $$ ("rmul" $$ "n" $$ "y"))))
  , ("fac",    "fix" $$ ("rfac" ! "x" ! "x" $$ "one" $$ ("n" ! "mul" $$ "x" $$ ("rfac" $$ "n"))))
  , ("eqnat",  "fix" $$ ("reqnat" ! "x" ! "y" ! "x" $$ ("y" $$ "True" $$ ("const" $$ "False")) $$ ("x1" ! "y" $$ "False" $$ ("y1" ! "reqnat" $$ "x1" $$ "y1"))))
  , ("sumto",  "fix" $$ ("rsumto" ! "x" ! "x" $$ "Zero" $$ ("n" ! "add" $$ "x" $$ ("rsumto" $$ "n"))))
  , ("n5",     "add" $$ "two" $$ "three")
  , ("n6",     "add" $$ "three" $$ "three")
  , ("n17",    "add" $$ "n6" $$ ("add" $$ "n6" $$ "n5"))
  , ("n37",    "Succ" $$ ("mul" $$ "n6" $$ "n6"))
  , ("n703",   "sumto" $$ "n37")
  , ("n720",   "fac" $$ "n6")
  , ("n4",     "add" $$ "two" $$ "two")
  , ("n21",    "sumto" $$ "n6")
  , ("n24",    "fac" $$ "n4")
  , ("n120",   "fac" $$ "n5")
  , ("n14",    "mul" $$ "two" $$ ("Succ" $$ "n6"))
  , ("n105",   "sumto" $$ "n14")
  ]
  (case n of
     0 -> "if" $$ "True" $$ "True" $$ "False"
     1 -> "eqnat" $$ "n5" $$ ("add" $$ "two" $$ "three")
     2 -> "eqnat" $$ "n24" $$ ("add" $$ "n21" $$ "three")
     3 -> "eqnat" $$ "n120" $$ ("add" $$ "n105" $$ ("Succ" $$ "n14"))
     4 -> "eqnat" $$ "n720" $$ ("add" $$ "n703" $$ "n17")
     _ -> error "cooked: expect [0..4]")

prettyPrec :: [String] -> Bool -> Int -> Tm String -> ShowS
prettyPrec _      d n (Var a)     = showString a
prettyPrec vs     d n (x `App` y) = showParen d $ 
  prettyPrec vs False n x . showChar ' ' . prettyPrec vs True n y
prettyPrec (v:vs) d n (Lam b)     = showParen d $ 
  showString "λ" .
  showString v . showString ". " . prettyPrec vs False n (instantiate1 (Var v) b)

prettyWith :: [String] -> Tm String -> String
prettyWith vs t = prettyPrec (filter (`notElem` toList t) vs) False 0 t ""

pretty :: Tm String -> String
pretty = prettyWith $ [ [i] | i <- ['a'..'z']] ++ [i : show j | j <- [1..], i <- ['a'..'z'] ]

pp :: Tm String -> IO ()
pp = putStrLn . pretty

noToTm :: No a -> Tm a
noToTm (Neutr x ts) = foldl App (Var x) (map noToTm ts)
noToTm (LamNo x b)  = lamP x (noToTm b)

test :: String -> Tm String -> IO ()
test name result = do
  putStrLn name
  if result == true
    then putStrLn "Result correct."
    else do
      putStrLn "Unexpected result:"
      pp result
      exitFailure

norm_vs_nbe n = do
  let t = cooked n
  putStrLn $ "level " ++ show n
  pp t
  test "norm" . noToTm . norm $ t
  test "nbe " . noToTm . nbe  $ t

main = do
  norm_vs_nbe 3
  norm_vs_nbe 4
