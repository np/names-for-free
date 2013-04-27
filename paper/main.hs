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
[keys|intro
      overview
      termStructure
      examples
      comparison
      performance
      proofs
      discussion
     |]

-- figures
-- [keys|TODO|]

-- citations
[keys|citeTODO|]

title = «Parametric Nested Abstract Syntax»
  -- «A Classy Kind of Nested Abstract Syntax»
-- Ingredients:
-- Classes
-- Polymorphism
-- Nested


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
  -- JP
  section $ «Intro» `labeled` intro
  subsection $ «Example final»
  
  -- JP
  section $ «Overview» `labeled` overview
  subsection $ «DeBruijn»
  subsection $ «Maybe/Nested»
  [agdaP|
  |type Succ a = Either a ()
  |              
  |data TmN a where
  |  Var :: a → TmN a
  |  App :: TmN a → TmN a → TmN a
  |  Lam :: TmN (Succ a) → TmN a
  |]
  subsection $ «Our stuff»
  subsection $ «Safety»
  p "the injection is always correct " $ «the injection is always correct if all binder types are universally quantified»
  subsection $ «Auto-inject»
  
  -- NP
  section $ «Term Structure» `labeled` termStructure
  p "" $ «Laws»
  subsection $ «Contexts, inclusion and membership»
  p "" $ «free theorems»
  p "auto-weakening, type-class hack" mempty
  subsection $ «Renaming/Functor»
  subsection $ «Substitute/Monad»
  subsection $ «Traversable»

  -- JP/NP
  section $ «Examples» `labeled` examples
  p "double-style remark" «»
  subsection $ «size»
  subsection $ «free variables» -- maybe lift this upwards.
  subsection $ «member of»
  subsection $ «η?»
  subsection $ «α-eq»
  subsection $ «nbe»
  subsection $ «CPS»
  subsection $ «closure conversion»

  -- NP
  section $ «Comparisons» `labeled` comparison
  subsection $ «Fin»
  subsection $ «Maybe/Nested»
  p "" $ «Kmett's succ-less»
  subsection $ «PHOAS»
  subsection $ «HOAS»
  p "" «Functions should only be substitutions»
  subsubsection $ «Concrete Terms»
  p "" «TmH → TmH | TmH × TmH»
  p "+" «Exotic terms»
  p "+" «Negative occurences of the recursive type»
  subsection $ «Syntax for free»
  p "+" «Forced to use catamorphism to analyse terms»
  subsection $ «McBride's "Classy Hack"»
  subsection $ «NaPa/NomPa»
  subsection $ «Multiple Binders/Rec/Pattern/Telescope»

  -- ??
  section $ «Performance» `labeled` performance
  p "" «fv, nbe, ?»

  -- ??
  section $ «Proofs» `labeled` proofs
  p "" «isomorphisms, free-theorems»

  -- JP
  section $ «Discussion» `labeled` discussion
  p "non-intrusive" «the approach can be used locally»
  p "" «more remarks about safetly»
  p "" «impredicativity»
  p "getting rid of the injections by using a stronger type system" «»

  p "acknowledgements" «Emil Axelsson wrote a definition of catamorphism on untyped lambda terms.»  
  
  itemize $ do 
--    it «PHOAS»
--    it «Functor/Monad/Categorical structure»
--    it «Traversable»
 --   it «Maybe»
 --   it «succ-less (Kmett)» -- http://www.slideshare.net/ekmett/bound-making-de-bruijn-succ-less
    it «isomorphisms»
 --   it «safety»
 --   it «Worlds»
    it «free theorem: world-polymorphic term functions»
 --   it «example programs (fv, eta?, nbe, CPS, closure-conv.)»
--    it «type-class coercions»
--    it «performance benchmark (fv, nbe)»
--    it «functions are only substitutions»
  --  it «our binder is closest to the "real meaning" of bindings»
 --   it «shallow interface/smart constructors»
--    it «mcbride "classy hack"»
--    it «"free" substitutions»

appendix = execWriter $ do
  return ()
-- }}}

main = do -- {{{
  let base = "out"
  writeAgdaTo "PaperCode.hs" $ doc
  quickView myViewOpts{basedir=base,showoutput=False,pdfviewer="echo"} "paper" doc

doc = document title authors keywords abstract body appendix
-- }}}

-- vim: foldmarker
