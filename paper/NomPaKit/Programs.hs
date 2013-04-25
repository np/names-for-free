{-# OPTIONS -fno-warn-name-shadowing #-}
module NomPaKit.Programs where

import NomPaKit.DSL
import NomPaKit.Basics (assertEq)
import Data.Tree

id3TreeN :: (MAGIC r, LET r, APP r, LAM r) => r (a -> a)
id3TreeN =
  letH "id" (lam "x" $ \x -> x) $ \id' ->
    magic id' `app` (lam "x" $ \x -> id' `app` x)

id3TreeD :: T a
id3TreeD =
  letD (lamD $ varD 0) $
       varD 0 `app` (lamD $ varD 1 `app` varD 0)

ex6times7 :: (OPS r, LET r) => r ℕ
ex6times7 =
  letH "x" (num 6) $ \x ->
  letH "y" (x +: num 1) $ \y ->
  x *: y

ex6times7D :: (OPS r, DB r) => r ℕ
ex6times7D =
  letD (num 6) $
  letD (varD 0 +: num 1) $
  varD 1 *: varD 0

printHello2times21 :: OPS r => r Interactive
printHello2times21 =
  printT (text "Hello! 2 times 21 is equal to ") >>:
  printT (showT (num 2 *: num 21))

printHello2times21FR :: OPS r => r Interactive
printHello2times21FR =
  printT (text "Bonjour ! 2 fois 21 est égal à ") >>:
  printT (showT (num 2 *: num 21))

aStringList :: OPS r => r [String]
aStringList = list [text "a", text "b" ++: text "c", showT (num 2 +: num 3)]

ex2x10x11 :: OPS r => r ℕ
ex2x10x11 = num 2 *: (num 10 +: num 11)

abcTree :: Tree String
abcTree = node "A" [ node "B" [] , node "C" [] ]

abcTreeProg :: OPS r => r (Tree String)
abcTreeProg = symLift abcTree

manyNodes :: (LET r, OPS r) => r (Tree ℕ)
manyNodes =
  letH "x₀" (num 42 ∸ (num 2 *: num 21)) $ \x0 ->
  letH "x₁" (nodeT x0 (list [])) $ \x1 ->
  letH "x₂" (nodeT (num 1) (list [ x1 , x1 ])) $ \x2 ->
  letH "x₃" (nodeT (num 2) (list [ x2 , x2 ])) $ \x3 ->
  letH "x₄" (nodeT (num 3) (list [ x3 , x3 ])) $ \x4 ->
  nodeT (num 4) (list [ x4 , x4 ])

printMeFirstThen :: OPS r => r Interactive
printMeFirstThen =
  printT (text printMeFirst) >>: printT (text thenPrintMe)

printMeFirst, thenPrintMe :: String
printMeFirst = "Print me first."
thenPrintMe  = "Then print me."

abcdefTree :: Tree String
abcdefTree =
   node "A" [ node "B" []
            , node "C" [ node "D" [] , node "E" [] ]
            , node "F" [] ]

ex85 :: (LET r, OPS r) => r ℕ
ex85 =
  letH "x" (num 1) $ \x ->
  x {- ici x égale 1 -} +:
  (letH "x" (num 2) $ \x ->
  x {- ici x égale 2 -} +:
  ((letH "x" (num 3) $ \x -> {- ici x égale 3 -} x) +:
  x {- ici x égale 2 -} +:
  (letH "x" (num 11 *: x) {- ici x égale 2 -} $ \x ->
  x {- ici x égale 22 -} +:
  (letH "x" (letH "x" (num 5) $ \x -> num 11 *: x {- ici x égale 5 -}) $ \x ->
  x {- ici x égale 55 -}))))

ex85res :: ℕ
ex85res = assertEq 85 (unR ex85)
