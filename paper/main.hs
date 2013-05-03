{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim

import Language.LaTeX

import System.Cmd (system)
import System.Directory (doesFileExist)
import Control.Monad.Writer hiding (when)

import Language.LaTeX.Builder.QQ (texm, texFile)

import Kit (document, itemize, it, dmath, {-pc, pcm,-} footnote, writeAgdaTo, startComment, stopComment, indent, dedent, citet)
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
[keys|pouillard_unified_2012
      mcbride_am_2010
     |]

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
  notetodo «ACM classification (JP: no clue how it's done these days!)»
  section $ «Intro» `labeled` intro
  subsection $ «Example final»
  
  -- JP
  section $ «Overview» `labeled` overview
  -- subsection $ «DeBruijn Indices»
  p""«A common way to represent variables is by the number of variables bound 
      between the occurence of a given variable {|x|} and its declaration.»
  notetodo «cite»
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
  notetodo «cite»
  [agdaP|
  |data a ▹ b = There a | Here b 
  |type Succ a = a ▹ ()
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
  |constN = Lam $ Lam $ Var (There (Here ()))
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
  notetodo «Frame this?»
  [agdaP|
  |data Tm w where
  |  Var :: w → Tm w
  |  App :: Tm w → Tm w → Tm w
  |  Lam :: (∀ v. v → Tm (w ▹ v)) → TmN a
  |]
  p""«That is, instead of adding a concrete unique type in the recursive parameter of {|Lam|}, 
      we quantify universally over a type variable {|v|} and add this type variable to the type of free variables.»
  p""«We also provide the sub-term with an arbitrary value of type {|v|}, to be used at occurences of the variable bound by {|Lam|}. »

  p""«The constant function is then represented as follows:»
  [agdaP|
  |const_ :: Tm
  |const_ = Lam $ \x → Lam $ \y → Var (There (Here x))
  |]

  -- subsection $ «Safety»
  p""«Now, if one makes a mistake and forgets one {|There|} when typing the term, GHC rejects the definition.»
  [agdaP|
  |oops_ = Lam $ \x → Lam $ \y → Var (Here x) 
  |-- Couldn't match expected type `v1' with actual type `v'
  |]

  p""«In fact, the possibility of making a mistake is inexistant (if we ignore diverging terms).»

  p""«Indeed, because the type {|v|} corresponding to a bound variable is universally quantified, 
      the only way to construct a value of its type is to use the variable bound by {|Lam|}.»
  p""«Conversely, in a closed context, if one considers the expression {|Var (f x)|}, only one possible value of {|f|} 
      is admissible. Indeed, any context, the type of variables is {|w = w0 ▹ v0 ▹ v1 ▹ ⋯ ▹ vn|} where {|v0|}, {|v1|}, … , {|vn|} 
      are all distinct and universally quantified, and none of them occurs as part of {|w0|}. 
      Hence, there is only one injection function from a given {|vi|} to {|w|}.»

  -- subsection $ «Auto-inject»
  p""«Knowing that the injection functions are purely mechanical, one may wish to automate them.
      Thanks the the powerful instance search mechanism implemented in GHC, this is feasible. 
      We can define a class {|v ∈ w|} capturing that {|v|} occurs as part of a context {|w|}:»
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

  p""«Our term representation allows to construct terms with DeBruijn-indices, 
      combined with the safety and convenience of named variables. These advantages
      extend to the analysis and manipulation on terms.

   Indeed, because the representation contains both concrete indices and functions at
   bindinding sites, one can take advantage of either aspect when analysing and manipulating terms.

   One can take the example of a size function to illustrate this flexibility. A first way to compute the size of a term
   is to arrange to substitute each variable occurence by its size (the constant 1 for the purpose of this example).
   This can be realised by applying the constant 1 at every function argument of a Lam constructor. One then needs
   to adjust the type to forget the difference between the new variable and the others. The variable and application
   cases then offer no surprises. (We defer the description of the functor instance to the next section.)
   »

  [agdaP|
  |size1 :: Term Int -> Int
  |size1 (Var x) = x
  |size1 (Lam _ g) = 1 + size1 (fmap untag (g 1))
  |size1 (App t u) = 1 + size1 t + size1 u
  |]

  p""«
   An other way to proceed is to simply pass a dummy object to the function arguments of Lam, and
   use only the deBruijn index to compute results in the case of variables. Using this technique,
   the size computation looks as follows:
   »

  [agdaP|
  |size2 :: Term a -> Int
  |size2 (Var _) = 1
  |size2 (Lam g) = 1 + size2 (g ())
  |size2 (App t u) = 1 + size2 t + size2 u
  |]

  p""«
   One may however chose to combine the two approaches. 
   This time we also assume an arbitrary environment 
   mapping free variables to a size. For each new variable,
   we pass the size that we want to assign to it to the binding function, and 
   we extend the environment to use that value on the new variable, or
   lookup in the old environment otherwise.
   »

  [agdaP|  
  |size :: (a -> Int) -> Term a -> Int
  |size f (Var x) = f x
  |size f (Lam _ g) = 1 + size (extend f) (g 1)
  |size f (App t u) = 1 + size f t + size f u
  |]
  [agdaP|  
  |extend g (Here a) = a
  |extend g (There b) = g b
  |]

  subsection $ «Catamorphism»
  p""«This pattern can be generalized to any algebra over terms, yielding the following catamorphism over terms.
      Note that the algebra corresponds to the higher-order representation of lambda terms.»
  [agdaP|
  |type Algebra w a = (w → a, (a → a) → a, a → a → a)
  |cata :: Algebra w a → Term w → a
  |cata φ@(v,l,a) s = case s of
  |   Var x   → v x
  |   Lam f   → l (cata (extend v,l,a) . f)
  |   App t u → a (cata φ t) (cata φ u)
  |]

  subsection $ «DeBruijn indices as names»
  -- our debruijn indices are typed with the context where they are valid.
  -- If that context is sufficently polymorphic, they can not be mistakenly used in a wrong context.
  -- a debruijn index in a given context is similar to a name.


  p "" «A common use case is that one wants to be able to check if an occurence of
        a variable is a reference to some previously bound variable. 
        With deBruijn indices, one must (yet again) count the number of binders traversed 
        between the variable bindings and its potential occurences --- as error prone as it gets.
        Here as well, we can take advantage of polymorphism to ensure 
        that no mistake happens. We provide a combinator {|unpack|}, which transforms
        a binding structure
        (of type {|forall v. v → Tm (w :▹ v)|}) into a sub-term with one more free variable 
        {|Tm (w :▹ v)|} and a value (called {|x|} below) of type {|v|}, where {|v|} is 
        bound existentially. We write the combinator in CPS in order to encode the existential:
        »
  [agdaP|
  |unpack :: (forall v. v → Tm (w ▹ v)) → 
  |          (forall v. v → Tm (w ▹ v) → a) → a
  |]

  p "" «     
        Because {|v|} is existentially bound and occurs only positively in {|Tm|}, {|x|}
        can never be used in a computation. It acts as a reference to a variable in a context,
        but in a way which is only accesible to the type-checker.

        That is, when facing for example a term {|t|} of type {|Tm (w ▹ v ▹ a ▹ b)|}, {|x|}
        refers to the third free variable in {|t|}.

        Using {|unpack|}, one can write a function recognising an eta-contractible term as follows:
        (Recall that an a eta-contractible term has the form {|\x → e x|}, where {|x|} 
        does not occur free in {|e|}.)
        »

  [agdaP|
  |canEta :: Term Zero → Bool
  |canEta (Lam e) = unpack e $ \x t → case t of
  |  App e1 (Var y) → y `isOccurenceOf` x && 
  |                   not (x `occursIn` e1)
  |  _ → False
  |canEta _ = False
  |]

  p "" «In the above example, the functions {|isOccurenceOf|} and {|occursIn|} use the {|inj|}
        function to lift {|x|} to a reference in the right context before comparing it to the
        occurences.
        The occurence checks do not get more complicated in the presence of multiple
        binders. For example, the code which recognises the pattern {|\x y → e x|} is
        as follows:»

  [agdaP|
  |recognize :: Term Zero → Bool
  |recognize t0 = case t0 of 
  |    Lam f → unpack f $ \x t1 → case t1 of
  |      Lam g → unpack g $ \y t2 → case t2 of
  |        App e1 (Var y) → y `isOccurenceOf` x && 
  |                         not (x `occursIn` e1)
  |        _ → False   
  |      _ → False   
  |    _ → False   
  |]

  p""«Again, even though our representation is a variant of DeBruijn indices, the use of polymorphism
      allows to refer to variables by name, while remaining safe.»

  -- NP
  section $ «Term Structure» `labeled` termStructure
  p "" $ «Laws»
  subsection $ «Contexts, inclusion and membership»
  p "" $ «free theorems»
  p "auto-weakening, type-class hack" mempty
  subsection $ «Renaming/Functor»
  subsection $ «Substitute/Monad»
  subsection $ «Traversable»
  subsection $ «Unpack»
  
  [agdaP|
  |unpack b k = k fresh (b fresh)
  |fresh = error "cannot query fresh variables!"
  |]

  -- JP/NP
  section $ «Bigger Examples» `labeled` examples

  subsection $ «free variables»
  [agdaP|
  |rm :: [w ▹ a] → [w]
  |rm xs = [x | There x <- xs]
  |
  |freeVars :: Term w → [w]
  |freeVars (Var x) = [x]
  |freeVars (Lam f) = unpack f $ \ _ t → rm $ freeVars t
  |freeVars (App f a) = freeVars f ++ freeVars a
  |]

  subsection $ «Occurence Test»

  [agdaP|
  |instance Eq w => Eq (w ▹ v) where
  |  Here _ == Here _ = True
  |  There x == There y = x == y
  |  _ == _ = False
  |]

  [agdaP|
  |occursIn :: (Eq w, v :∈ w) => v -> Term w -> Bool
  |occursIn x t = lk x `elem` freeVars t
  |
  |isOccurenceOf :: (Eq w, v :∈ w) => w -> v -> Bool
  |isOccurenceOf x y = x == lk y
  |]

  subsection $ «Test of α-equivalence»
  p""«
   Testing for α-equivalent terms is straightforward. Our representation contains debruijn indices, so
   we only need to ignore the higher-order aspect. This can be done by simply applying dummy elements
   at every binding site. Additionally, as a natural refinement over the mere α-equivalence test, we allow
   for an equality test to be supplied for free variables. This equality test is provided by an {|Eq|} instance:
   »

  [agdaP|
  |instance Eq w => Eq (Term w) where
  |  Var x == Var x' = x == x'
  |  Lam g == Lam g' = g () == g' ()
  |  App t u == App t' u' = t == t' && u == u'        
  |]  

  subsection $ «Normalisation by evaluation»
  [agdaP|
  |eval :: Term v -> Term v
  |eval (Var x) = Var x
  |eval (Lam n t) = Lam n (eval . t)
  |eval (App t u) = app (eval t) (eval u)
  |
  |app :: Term v -> Term v -> Term v
  |app (Lam _ t) u = subst0 =<< t u 
  |app t u = App t u
  |
  |subst0 :: v :▹ Term v -> Term v
  |subst0 (Here x) = x
  |subst0 (There x) = Var x
  |]

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
  
  -- the point of types isn’t the crap you’re not allowed to write,
  -- it’s the other crap you don’t want to bother figuring out.

  p "" «{citet[mcbrideam2010]} has devised a set of combinators to construct 
        lambda terms in de Brujin representation, with the ability to refer to 
        bound variables by name. Terms constructed using McBride's technique are 
        textually identical to terms constructed using ours. Another point of 
        similiarity is the use of instance search to recover the indices from a 
        host-language variable name.

        Even though McBride's combinators use polymorphism in a way similar to ours,
        a difference is that they produce a plain de Brujin representation, 
        while we keep the polymorphism throughout.

        Another difference is that McBride integrate the injection in the abstraction
        constructor rather than the variable one. The type of the {|var|} combinator becomes then
        simpler, at the expense of {|lam|}:
        »
  [agdaP|
  |lam :: ((∀ n. (Leq (S m) n ⇒ Fin n)) → Term (S m))
  |        → Term m
  |var :: Fin n → Term n
  |]
  p "" «The above types also reveal somewhat less precise types that what we use.
        Notably, the {|Leq|} class captures only one aspect of context inclusion (captured by the class {|:<|}
        in our development),
        namely that one context should be smaller than another.
        This means, for example, that the class constraint {|w :< w'|} can be meaning fully resolved
        in more cases than {|Leq m n|}, in turn making functions such as {|wk|} more useful in practice.»

  subsection $ «NomPa (nominal fragment)»

  p""«{citet[pouillardunified2012]} describe an interface for names and binders which provides maximum safety.
      The library is writen in Agda, using dependent types. The interface makes use of an abstract notion 
      of {|World|}s (set of names), {|Binder|}s (name declaration), and {|Name|}s (the occurence of a name).

      A {|World|} can either be {|Empty|} or result of the addition of a {|Binder|} to an existing {|World|}, using the operator.
     »
  notetodo «Do not output this in "PaperCode.hs"» 
  [agdaP|
  |-- Abstract interface
  |World :: *
  |Binder :: * 
  |Name :: World → *
  |Empty :: World 
  |(◃) :: Binder → World → World
  |]

  p""«
  A {|Name|} set is indexed by a {|World|}: this ties occurences to the context where they make sense.
  On top of these abstract notions, one can construct the following representation of terms:
  »
  
  [agdaP|
  |data Tm α where
  |  Var :: Name α → Tm α
  |  App :: Tm α → Tm α → Tm α
  |  Lam :: (b :: Binder) → Tm (b ◃ α) → Tm α
  |]
  notetodo «The left-pointing triangle does not appear correctly »

  notetodo «The rest of the section is wrong.»
  p""«Our representation is an instance of Pouillard's NomPa framework, 
      where we instanciate the abstract interface as follows:»
  
  [agdaP|
  |World = *
  |Binder = (v :: *) × v
  |Name w = w
  |Empty = Zero
  |(v,_) ◃ w = w ▹ v
  |]

  p""«no loss of precision by doing this instanciation (?)»

  p""«export is replaced by unpack (?)»

  p""«After this instantiation, dependent types are no longer required --- but impredicativity is.»
  
  p""«Perhaps counter intuitively, our representation is an instance of the nominal fragment of NomPa,
      while it appears to be closer to a DeBruijn representation. 
      This suggests that the ``DeBruijn'' fragment of NomPa could be made 
      closer to the nominal fragment by using the ideas of this paper.
      »

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

  p "getting rid of the injections by using a stronger type system" «
    We use the powerful GHC instance search in a very specific way: only to discover in injections. 
    This suggests that a special-purpose type-system (featuring a form of subtyping) 
    could be built to take care of those injections automatically.
    An obvious benefit would be some additional shortening of programs manipulating terms. 
    A more subtle one is that, since injections would not be present at all, the performance 
    would be increased. Additionally, this simplification of programs would imply an
    even greater simplification of the proofs about them; indeed, a variation in complexity in
    an object usually yields a greater variation in complexity in proofs about it.
  »

  p "acknowledgements" «We thank Emil Axelsson for discussions on name binding.»  
  
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
  let jpbib = "../../gitroot/bibtex/jp.bib"
  e <- doesFileExist jpbib
  unless (not e) $ do putStrLn "refreshing bib"
                      system $ "cp " ++ jpbib ++ " ." 
                      return ()
  let base = "out"
  writeAgdaTo "PaperCode.hs" $ doc
  quickView myViewOpts{basedir=base,showoutput=False,pdfviewer="echo"} "paper" doc

doc = document title authors keywords abstract body appendix
-- }}}

-- vim: foldmarker
-- -}