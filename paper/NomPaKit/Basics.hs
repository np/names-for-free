{-# LANGUAGE FlexibleInstances, QuasiQuotes #-}
module NomPaKit.Basics where

import qualified Data.Map as Map
import Data.List.Split (splitOneOf)
import Data.Monoid
import Data.Char (isAscii)
import Control.Monad.Writer
import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Math as M
import Language.LaTeX.Builder.QQ (keys, tex)
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder.Color as C
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Types (uncatParItm, unParNote)
import Text.PrettyPrint.Leijen (Doc, (<+>), (<$>))
import qualified Text.PrettyPrint.Leijen as P
import NomPaKit.Config

memoLookup :: Ord a => [(a,b)] -> a -> Maybe b
memoLookup list = (`Map.lookup` table)
  where table = Map.fromList list

fromRight :: Show a => Either a b -> b
fromRight = either (error . show) id

ma :: [MathItem] -> LatexItem
ma = B.math . mc

mc :: Monoid a => [a] -> a
mc = mconcat

infix 0 ↦
(↦) :: a -> b -> (a, b)
(↦) = (,)

haskellify :: String -> String
haskellify = concatMap θ
  where θ '☐' = " "
        θ ' ' = " "
        θ 'λ' = "\\"
        θ '∈' = ":∈"
        θ '⊆' = ":⊆"
        θ '▹' = ":▹"
        θ '‼' = ""
        θ  x  = [x]

put :: ParItem -> ParItemW
put = tell

-- would be useful is HLaTeX
{-
class Sub a where
  sub :: a -> a -> a
instance Sub MathItem where
  x `sub` y = x ⊕ M.sub y
instance Sub (LatexM LatexItm) where
  x `sub` y = x ⊕ B.textunderscore y --WRONG
-}
class Sup a where
  sup :: a -> a -> a
instance Sup MathItem where
  x `sup` y = x ⊕ M.sup y
instance Sup (LatexM LatexItm) where
  x `sup` y = x ⊕ B.textsuperscript y

assertEq :: (Show a, Eq a) => a -> a -> a
assertEq x y | x == y    = x
             | otherwise = error . unwords $ ["assertion failure:"
                                             ,show x,"is different from"
                                             ,show y]

txt :: String -> Doc
txt = P.text

encloseSepSpacy :: Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSepSpacy = encloseSepGen (<+>) (<$>)

encloseSepGen :: (Doc -> Doc -> Doc) -> (Doc -> Doc -> Doc) -> Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSepGen (<.>) (<..>) left right sep ds
    = case ds of
        []  -> left <.> right
        [d] -> left <.> d <.> right
        _   -> P.align (P.group (fold (<..>) (zipWith (<.>) (left : repeat sep) ds)) <.> right)
  where
    fold _ []       = P.empty
    fold f xs       = foldr1 f xs

prettyShowString :: String -> String
prettyShowString = ($"") . prettyShowsString

prettyShowsString :: String -> ShowS
prettyShowsString xs = ('"':) . foldr (.) ('"':) (map ppOneChar xs)
 where
  ppOneChar c
    | isAscii c = ((init . tail . show $ [c])++)
    | otherwise = (c:)

hardline :: LatexItem
hardline = [tex|~\\~|]

-- shortcuts

[keys|paragraphName marginNote code diag sectioningOnly cutHere|]

marked :: (Key -> Bool) -> (ParItm -> Bool)
marked pr pa =
  case unParNote pa of
    Nothing        -> False
    Just (k, _, _) -> pr k

putMark :: Key -> ParItemW
putMark key = put $ BI.parNote key BI.nilNote ø

select :: ParItem -> ParItem
select = fmap $ mconcat . f . uncatParItm where
  f, selectSecOnly :: [ParItm] -> [ParItm]
  f [] = []
  f (x : xs) | marked (== sectioningOnly) x = selectSecOnly . f $ xs
             | marked (== cutHere) x        = []
             | otherwise                    = x : f xs

  selectSecOnly = filter (not . marked (const True))

parMarkCode :: ParItem -> ParItem
parMarkCode = BI.parNote code BI.nilNote

parMarkDiag :: ParItem -> ParItem
parMarkDiag = BI.parNote diag BI.nilNote

parMarkParaName :: String -> ParItem -> ParItem
parMarkParaName = BI.parNote paragraphName . BI.stringNote

namedPara :: String -> LatexItem -> ParItem
namedPara nam = parMarkParaName nam . B.para

marginpar :: LatexItem -> ParItem
marginpar = B.para . BI.latexCmdArg "marginpar"

array :: Rational -> [ParItemW] -> ParItemW
array k xs = B.para !$? (mapM_ (\x -> B.minipage B.bot (L.cm k) !$? x) xs)

-- do not cut on unbreakable spaces
breakableWords :: String -> [String]
breakableWords = filter (not.null) . splitOneOf " \t\n"

note :: LatexItem -> ParItemW
note
  | displayNotes config =
       put . BI.parNote marginNote (BI.stringNote"NOTE") . marginpar
           . C.fcolorbox fcolor bgcolor . B.minipage B.normal L.marginparwidth
           . B.para . B.decl B.scriptsize
  | otherwise = const (return ())
  where bgcolor = C.white
        fcolor = C.red
