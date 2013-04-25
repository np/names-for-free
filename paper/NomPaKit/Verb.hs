{-# LANGUAGE QuasiQuotes, PatternGuards #-}
module NomPaKit.Verb
  (verb, verbatim, myHstring, mathW, myCharToMath,
   firebrick, purple, mediumBlue, alignVert,
   {-agdaBaseCode,-} AgdaInput, colorizeAgdaP, {-agdaCode,-} agdaCodeI, agdaCodeIU, agdaCodeP, colorize) where

import Data.Maybe
import Data.Foldable (Foldable,foldMap)
import Data.List
import Data.String
import Control.Arrow (second)
import Control.Monad (ap)

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Builder.Color as C
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Builder.QQ (tex)

import NomPaKit.Basics
import NomPaKit.Config
import NomPaKit.Char
import ColorizeAgda (Color(RGB, CMYK), colorizeAgda, defaultColor, ParseError)
import qualified ColorizeAgda as CA

type MayAlign = (Rational, Pos) -> LatexItem -> LatexItem

align, dontAlign :: MayAlign
align (k, pos) = B.makebox (L.ex (k * 1.22)) pos
dontAlign = const id

wordBreakableCode :: (String -> LatexItem) -> String -> LatexItem
wordBreakableCode f = B.unwords . map f . breakableWords
  -- where breakableWords' x = if ' ' `elem` x then error "foo" else breakableWords x

-- let's customize the rendering of some characters in `verb' mode
myXchar :: MayAlign -> B.XChar -> B.XChar
myXchar mayAlign xchar = \x -> fromMaybe (defaultCase x) $ cache x
  where
    cache = memoLookup specialCases
    defaultCase x = maybe id mayAlign (widthPos x) (xchar x)
    specialCases =
      [('\n', myNewline)
      ,('☐',  mayAlign (1.5,B.flushLeft) [tex| |])
      ,('=',  B.ttchar '=')
      ,('{',  mayAlign (1,B.flushLeft)  $ M.mchar B.hchar '{')
      ,('}',  mayAlign (1,B.flushRight) $ M.mchar B.hchar '}')
      ,('(',  mayAlign (1,B.flushLeft)  . B.math $ M.lparen) -- mleft '('
      ,(')',  mayAlign (1,B.flushRight) . B.math $ M.rparen) -- mright ')'
      ]

-- The wordBreakable
verb :: Bool -> Bool -> String -> LatexItem
verb mayAlign wordBreakable = mayWordBreakCode $ B.texttt . B.spaceProtector verbChar
  where verbChar = myXchar (if mayAlign && not (sloppyAligns config) then align else dontAlign)
                           (myMchar (M.mchar B.ttchar))
    -- B.spaceProtector is useful even in word breakable code because of
    -- non breaking spaces that we have to preserve
        mayWordBreakCode | wordBreakable = wordBreakableCode
                         | otherwise     = id

verbatim :: Bool -> Bool -> String -> ParItemW
verbatim = qqP (verb True False) id

widths :: Fractional a => [(Pos, [(a, [Char])])]
widths =
  [B.flushLeft ↦
    [0.5 ↦ subscriptChars ++ superscriptChars
    ,3 ↦ "…"
    ]
  ,B.flushRight ↦
    []
  ,B.centered ↦
    [0.5 ↦ "⟨⟩"
    ,1   ↦ "|- ∀αβδγε◅·ƛ_↑øℓ∈∷ΓΠ⟦⟧⟪⟫●∸ν⊢⊥⊤×Δ<>≥≤"
    ,1.5 ↦ "⊆∨∧¬ℕ⟶⊎Λℛ↦𝔼ℙ"]
  ]

widthPos :: Char -> Maybe (Rational, Pos)
widthPos =
  memoLookup [ (c,(w,pos))
             | (pos,wcss) <- widths
             , (w, cs)    <- wcss
             , c          <- cs
             ]

-- takes the highest character to vertically align them all.
myStrut :: LatexItem
myStrut = B.vphantom (BI.rawTex "$\\{$")

alignVert, alignVert' :: LatexItem -> LatexItem
alignVert = (⊕ myStrut)
alignVert' = (myStrut ⊕)

myNewline :: LatexItem
myNewline = alignVert $ B.decl (B.nopagebreak Nothing) (BI.latexCast . BI.parItem $ B.newline ø)
{-
myNewline = alignVert $ nopagebreak' (BI.latexCast . BI.parItem $ B.newline ø)
  where nopagebreak' x = -- [tex|\penalty-10000|] ⊕ x
                       BI.rawDecls [B.nopagebreak Nothing] ⊕ x
-}

-- Tell if the list have adjacent equal elements
adjDups :: Eq a => [a] -> [a]
adjDups = map fst . filter (uncurry (==)) . (zip`ap`tail)

  -- Ideas: balance: (){}[]“”
checkTypos :: String -> String
checkTypos x
  | doCheckTypos config =
      case adjDups . words $ x of
        [] -> x
        xs -> error $ "dup words " ++ show xs ++ " in " ++ show x
  | otherwise = x

myHstring :: String -> LatexItem
myHstring s
  | null s    = ø
  | otherwise = f s where
     f = foldMap myHchar . concat . intersperse (fromString "\n")
                         . filter (not . null) . lines . checkTypos

-- Agda
type AgdaInput = [(String, Maybe Color)]

rebuildAgdaInput :: AgdaInput -> String
rebuildAgdaInput = mc . map fst

colorizeAgdaBase :: String -> Either ParseError AgdaInput
colorizeAgdaBase = fmap (map (second (defaultColor =<<))) . colorizeAgda

colorizeAgdaP :: String -> Either ParseError AgdaInput
colorizeAgdaP
  | sloppyErrors config || noColors config
    = \i -> Right [(i, Nothing)]
  | otherwise
    = colorizeAgdaBase

colorizeDynAgdaP :: AgdaInput -> Either ParseError AgdaInput
colorizeDynAgdaP
  | sloppyErrors config && colorful config
    = colorizeAgdaBase . rebuildAgdaInput
  | otherwise
    = Right -- coloring already done

-- agdaCode :: String -> LatexItem
-- agdaCode = agdaCodeI . fromRight . colorizeAgdaP

-- 'U' as in unaligned
agdaCodeIU :: AgdaInput -> LatexItem
agdaCodeIU = agdaBaseCode True False

agdaCodeI :: AgdaInput -> LatexItem
agdaCodeI = agdaBaseCode True True

qqP :: (a -> LatexItem) -> (a -> String) -> Bool -> Bool -> a -> ParItemW
qqP toLatex toString leadingHardline indent x
  = put . parMarkCode . B.para
  . (if indent then id else (B.noindent ⊕))
  . (B.comment (substNbsp (toString x)) ⊕)
  . (if leadingHardline then (hardline ⊕) else id)
  . alignVert'
  $ toLatex x

agdaCodeP :: Bool -> Bool -> AgdaInput -> ParItemW
agdaCodeP = qqP (agdaBaseCode False True) rebuildAgdaInput

color2color :: Color -> C.Color
color2color (CMYK c y mag k) = C.cmyk c y mag k
color2color (RGB r g b) = C.rgb (f r) (f g) (f b)
  where f y = fromIntegral y / (2 ^ (16 :: Integer))

firebrick, purple, mediumBlue :: C.Color
firebrick  = color2color CA.firebrick
purple     = color2color CA.purple
mediumBlue = color2color CA.mediumBlue

colorize :: LatexItem -> Maybe Color -> LatexItem
colorize x mcolor =
  case mcolor of
    Nothing  -> x
    Just col@CMYK{} -> B.textbf (C.textcolor (color2color col) x) -- ugly special case
    Just col -> C.textcolor (color2color col) x

agdaBaseCode :: Bool -> Bool -> AgdaInput -> LatexItem
agdaBaseCode wordBreakable mayAlign
    = {-alignVert' .-} mc . map (uncurry (skipSpaces (colorize . verb mayAlign wordBreakable))) . fromRight . colorizeDynAgdaP
  where skipSpaces f xs c | wordBreakable && all (`elem` " \n") xs = B.space
                          | otherwise                              = f xs c
{- NEW code but maybe broken
  = mc . map (uncurry (colorize . verb mayAlign wordBreakable)) . fromRight . colorizeDynAgdaP
-}

-- * this could support spaces
-- * we could avoid multiple B.math or rely on them being fused.
myMathString :: Foldable t => t Char -> LatexItem
myMathString = foldMap $ myMchar (B.math . myCharToMath)

myCharToMath :: Char -> MathItem
myCharToMath c
  | c `elem` "-.{}[]()*+|<>"   = BI.rawMath [c] -- BI.rawMathChar c
  | Just x <- M.charToMath c = x
  | otherwise                = error $ "NomPaKit.mathString: " ++ show c

-- Maths
mathW :: String -> LatexItem
mathW     = B.unwords . map myMathString . breakableWords
         -- we could use only mathString
