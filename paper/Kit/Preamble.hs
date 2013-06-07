{-# LANGUAGE QuasiQuotes, OverloadedStrings,
             FlexibleInstances, TemplateHaskell,
             NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Kit.Preamble where

import Prelude hiding (words)

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
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Builder.QQ (qp,tex)
import Language.LaTeX.Slicer (slice)
import Kit.QQ
import Kit.Basics

usepackage :: [String] -> String -> PreambleItem
usepackage xs = BI.usepackage (map BI.rawAnyTex xs) . BI.pkgName

fonts :: PreambleItem
fonts = usepackage [] "amssymb"
      ⊕ usepackage [] "amsmath"
      -- ⊕ usepackage [] "MnSymbol"
      ⊕ usepackage [] "epsdice"
      ⊕ usepackage [] "bbm"
      -- ⊕ usepackage [] "bbding"   -- to get Ellipse => BROKEN
      ⊕ usepackage [] "dsfont"   -- to get mathds => not enough symbols
      ⊕ usepackage [] "stmaryrd" -- To get {ll,rr}bracket
      -- ⊕ usepackage ["T3","OT1"] "fontenc"

      -- These two declarations are from the tipa package.
      -- However importing the packages breaks the document.
      -- Note that we require T3 fonts here. (we prefix our version with 'np')
      ⊕ [qp|\DeclareTextSymbol\nptextcrlambda{T3}{172}
           |\DeclareTextSymbolDefault\nptextcrlambda{T3}
           |]
      -- (like with tipa above)
      -- Take just a symbol from mathabx (prefixed with 'np')
      -- /usr/share/texmf-dist/tex/generic/mathabx/mathabx.dcl
      ⊕ [qp|\DeclareFontFamily{U}{npmathb}{\hyphenchar\font45}
           |\DeclareFontShape{U}{npmathb}{m}{n}{
           |      <5> <6> <7> <8> <9> <10> gen * mathb
           |      <10.95> mathb10 <12> <14.4> <17.28> <20.74> <24.88> mathb12
           |      }{}
           |\DeclareSymbolFont{npmathb}{U}{npmathb}{m}{n}
           |\DeclareFontSubstitution{U}{npmathb}{m}{n}
           |\DeclareMathSymbol{\npbigstar}   {2}{npmathb}{"0E} % to fool the highlighter => "
           |\DeclareMathSymbol{\npdotdiv}    {2}{npmathb}{"01} % to fool the highlighter => "
           |
           |\DeclareFontFamily{U}{matha}{\hyphenchar\font45}
           |\DeclareFontShape{U}{matha}{m}{n}{
           |      <5> <6> <7> <8> <9> <10> gen * matha
           |      <10.95> matha10 <12> <14.4> <17.28> <20.74> <24.88> matha12
           |      }{}
           |\DeclareSymbolFont{matha}{U}{matha}{m}{n}
           |\DeclareFontSubstitution{U}{matha}{m}{n}
           |\DeclareMathSymbol{\npoasterisk} {2}{matha}{"66} % to fool the highlighter => "
           |\DeclareMathSymbol{\npnotequiv}  {3}{matha}{"19} % to fool the highlighter => "
           |]
