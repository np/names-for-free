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

notetodo x = p"" $ red «TODO {x}»
--notecomm x = p"" $ red «COMMENT {x}»
-- notetodo _ = return ()
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
  -- JP (when the rest is ready)
  section $ «Intro» `labeled` intro
  subsection $ «Example final»
  
  -- JP
  section $ «Overview» `labeled` overview
  -- subsection $ «DeBruijn Indices»
  p""«A common way to represent variables is by the number of variables bound 
      between the occurence of a given variable {|x|} and its declaration.»
  todo «cite»
  p""«The main advantage of the technique two α-equivalent terms have exactly the same representation.»
  p""«A direct implementation of the technique may yield the following represtenation of untyped lambda terms:»
  [agdaP|
  |data Nat = Zero | Succ Nat
  |data TmDB where
  |  Var :: Nat → TmDB
  |  App :: TmDB → TmDB → TmDB
  |  Lam :: TmDB → TmDB
  |]
  p""«Using this representation, the representation of the constant function {|\x y -> x|} is the following:»
  [agdaP|
  |constDB :: TmDB
  |constDB = Lam $ Lam $ Var (Succ Zero)
  |]

  p""«However, such a direct implementation is naïve. It cannot distinguish between open and closed terms. 
      That is, a closed term has the same type as an open term.»

  -- subsection $ «Nested Abstract Syntax»
  p""«In Haskell, it is possible to remedy to this situation by "nested recursion". 
      That is, one parameterises the type of terms by a type that can represent free variables.
      If the parameter is the empty type, terms are closed. If the parameter is the unit type, there is one free variable, etc.»
  p""«This representation in known as Nested Abstract Syntax»
  todo «cite»
  [agdaP|
  |data a ⊕ b = Inl a | Inr b
  |type Succ a = a ⊕ ()
  |              
  |data TmN a where
  |  Var :: a → TmN a
  |  App :: TmN a → TmN a → TmN a
  |  Lam :: TmN (Succ a) → TmN a
  |]
  p""«The recursive case {|Lam|} changes the parameter type, increasing its cardinality by one.»

  p""«Using this representation, the representation of the constant function {|\x y → x|} is the following:»
  [agdaP|
  |data Zero -- no constructor
  |constN :: TmN Zero
  |constN = Lam $ Lam $ Var (Inl (Inr ()))
  |]
  p ""«As promised, the type is explicit about {|constN|} being closed.»
  p "" «In passing, we remark that another valid type for closed terms is {|∀ a. TmN a|} 
       --- literally: the type of terms which have an unknown number of free variables.
       Indeed, because {|a|} is universally quantified, there is no way to construct an inhabitant of it; 
       one cannot possibly refer to any free variable.»
  p""«Another drawback of using DeBruijn indices is that it is easy to make a mistake
      when counting the number of binders between the declaration of a variable and its occurence.»

  -- subsection $ «Our stuff»
  p""«To address this issue, we propose the following representation:»
  [agdaP|
  |data Tm w where
  |  Var :: w → Tm w
  |  App :: Tm w → Tm w → Tm w
  |  Lam :: (∀ v. v → Tm (w ⊕ v)) → TmN a
  |]
  p""«That is, instead of adding a concrete unique type in the recursive parameter of {|Lam|}, 
      we quantify universally over a type variable {|v|} and add this type variable to the type of free variables.»
  p""«We also provide the sub-term with an arbitrary value of type {|v|}, to be used at occurences of the variable bound by {|Lam|}. »

  p""«The constant function is then represented as follows:»
  [agdaP|
  |const_ :: Tm
  |const_ = Lam $ \x → Lam $ \y → Var (Inl (Inr x))
  |]

  -- subsection $ «Safety»
  p""«Now, if one were to make a mistake and forget one {|Inl|} when typing the term, GHC rejects the definition.»
  [agdaP|
  |oops_ = Lam $ \x → Lam $ \y → Var (Inr x) 
  |-- Couldn't match expected type `v1' with actual type `v'
  |]

  p""«In fact, the possibility of making a mistake is inexistant (if we ignore diverging terms).»

  p""«Ineed, because the type {|v|} corresponding to a bound variable is universally quantified, 
      the only way to construct a value of its type is to use the variable bound by {|Lam|}.»
  p""«Conversely, in a closed context, if one considers the expression {|Var (f x)|}, only one possible value of {|f|} 
      is admissible. Indeed, any context, the type of variables is {|w = w0 ⊕ v0 ⊕ v1 ⊕ ⋯ ⊕ vn|} where {|v0|}, {|v1|}, … , {|vn|} 
      are all distinct and universally quantified, and none of them occurs as part of {|w0|}. 
      Hence, there is only one injection function from a given {|vi|} to {|w|}.»

  -- subsection $ «Auto-inject»
  p""«Knowing that the injection functions are purely mechanical, one may wish to automate them.
      Thanks the the powerful class mechanism of Haskell, this is feasible. 
      We can define a class {|v ∈ w|} capturing that {|v|} occurs as part of a sum {|w|}:»
  [agdaP|
  |class v ∈ w where
  |  inj :: v → w
  |]  
  p""«We can then wrap the injection function and {|Var|} in a convenient package:»
  [agdaP|
  |var :: forall v w. (v ∈ w) => v → Tm w
  |var = Var . inj
  |]
  p""«and the constant function can be conveniently written:»
  [agdaP|
  |const_ :: Tm
  |const_ = Lam $ \x → Lam $ \y → var x
  |]

  p""«In sum, our term representation allows to write terms with DeBruijn-indices, 
      but hides the complexity of juggling with indices.»

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
-- -}