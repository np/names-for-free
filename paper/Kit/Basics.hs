{-# LANGUAGE FlexibleInstances, QuasiQuotes #-}
module Kit.Basics where

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
import Kit.Config

[keys|paragraphName code|]

put :: ParItem -> ParItemW
put = tell

infix 0 ↦
(↦) :: a -> b -> (a, b)
(↦) = (,)

memoLookup :: Ord a => [(a,b)] -> a -> Maybe b
memoLookup list = (`Map.lookup` table)
  where table = Map.fromList list

-- do not cut on unbreakable spaces
breakableWords :: String -> [String]
breakableWords = filter (not.null) . splitOneOf " \t\n"

parMarkCode :: ParItem -> ParItem
parMarkCode = BI.parNote code BI.nilNote

parMarkParaName :: String -> ParItem -> ParItem
parMarkParaName = BI.parNote paragraphName . BI.stringNote

namedPara :: String -> LatexItem -> ParItem
namedPara nam = parMarkParaName nam . B.para

pagebreak = put . B.parDecl . B.pagebreak
nopagebreak = put . B.para $ B.decl (B.nopagebreak Nothing) ø
rawTexP = put . B.para . BI.rawTex

hardline :: LatexItem
hardline = [tex|~\\~|]

fromRight :: Show a => Either a b -> b
fromRight = either (error . show) id

ma :: [MathItem] -> LatexItem
ma = B.math . mc

mc :: Monoid a => [a] -> a
mc = mconcat

-- would be useful in HLaTeX
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
