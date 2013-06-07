{-# LANGUAGE QuasiQuotes, OverloadedStrings,
               FlexibleInstances, TemplateHaskell,
               NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module AgdaKit.Verb
   ({-agdaBaseCode,-} AgdaInput, colorizeAgdaP, {-agdaCode,-} agdaCodeI, agdaCodeIU, agdaCodeP, colorize, firebrick, mediumBlue, purple) where

import AgdaKit.Colorize (Color(RGB, CMYK), colorizeAgda, defaultColor, ParseError)
import qualified AgdaKit.Colorize as CA

import Prelude hiding (words)

import Control.Arrow
import Control.Monad.Writer hiding (lift)
import Data.List hiding (words)
import Data.List.Split (splitOneOf)
import Data.Maybe (maybeToList)
import Data.String (fromString)
import Data.Generics.Uniplate.Data (universeBi)

import Language.LaTeX

import Control.Applicative ((<$>))

import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Types as T
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Builder.Color as C
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Builder.QQ (qp,tex)
import Language.LaTeX.Slicer (slice)
import Kit.QQ
import Kit.Basics
import Kit.Config
import Kit.Verb

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

agdaBaseCode :: Bool -> Bool -> AgdaInput -> LatexItem
agdaBaseCode wordBreakable mayAlign
    = {-alignVert' .-} mc . map (uncurry (skipSpaces (colorize . verb mayAlign wordBreakable))) . fromRight . colorizeDynAgdaP
  where skipSpaces f xs c | wordBreakable && all (`elem` " \n") xs = B.space
                          | otherwise                              = f xs c
{- NEW code but maybe broken
  = mc . map (uncurry (colorize . verb mayAlign wordBreakable)) . fromRight . colorizeDynAgdaP
-}

substNbsp :: String -> String
substNbsp = filter ψ . map θ
  where θ '☐' = ' '
        θ ' ' = ' '
        θ  x  =  x
        ψ '‼' = False
        ψ  _  = True

agdaCodeP :: Bool -> Bool -> AgdaInput -> ParItemW
agdaCodeP = qqP (agdaBaseCode False True) (substNbsp . rebuildAgdaInput)

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
