{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim

import Language.LaTeX

import Control.Monad.Writer hiding (when)

import Language.LaTeX.Builder.QQ (texm, texFile)

import Kit (document, itemize, it, dmath, {-pc, pcm,-} footnote, writeAgdaTo, startComment, stopComment, indent, dedent)
import NomPaKit hiding (when)
import NomPaKit.QQ

--import qualified MiniTikz.Builder as D -- hiding (node)
--import MiniTikz.Builder (right, below, nodeDistance, oF, dnode, spath, scope)

--import System.Directory (copyFile)

-- sections
[keys|keyTODO
     |]

-- figures
-- [keys|TODO|]

-- citations
[keys|citeTODO|]

title = «TODO»

authors = [ («Jean-Philippe Bernardy» , «bernardy@chalmers.se» , «Chalmers University of Technology and University of Gothenburg»)
           ,(«Nicolas Pouillard»      , «npou@itu.dk»          , «IT University Copenhagen»)
          ]
abstract = [texFile|abstract|]
keywords = [texFile|keywords|]
_Agda's = «{_Agda}'s»

--notetodo x = p"" $ red «TODO {x}»
--notecomm x = p"" $ red «COMMENT {x}»
notetodo _ = return ()
--notecomm _ = return ()

long = True
short = not long
debug = False
when :: Bool -> ParItemW -> ParItemW
when True  x = x
when False _ = return ()

doComment :: ParItemW -> ParItemW
doComment x = startComment >> x >> stopComment

commentWhen :: Bool -> ParItemW -> ParItemW
commentWhen True  x = doComment x
commentWhen False x = x

body = {-slice .-} execWriter $ do -- {{{
  return ()

appendix = execWriter $ do
  return ()
-- }}}

main = do -- {{{
  let base = "out"
  -- writeAgdaTo "....agda" $ doc
  quickView myViewOpts{basedir=base,showoutput=False,pdfviewer="echo"} "paper" doc

doc = document title authors keywords abstract body appendix
-- }}}

-- vim: foldmarker
