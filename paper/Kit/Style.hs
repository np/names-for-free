{-# LANGUAGE QuasiQuotes, OverloadedStrings, TemplateHaskell, NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Kit.Style where

import Language.LaTeX hiding ((<>))
import Kit.Basics
import Kit.Config
import Kit.QQ
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Builder.Color as C
import Language.LaTeX.Builder.QQ (tex)

textcolor | colorful config = C.textcolor
          | otherwise       = const id

red = textcolor C.red
emph = B.emph
{-
commentColor = textcolor firebrick
idColor = textcolor mediumBlue
-}
