{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim

import Language.LaTeX

import System.Cmd (system)
import System.Directory (doesFileExist)
import Control.Monad.Writer hiding (when)

import Language.LaTeX.Builder.QQ (texm, texFile)

import Kit (document, itemize, it, dmath, {-pc, pcm,-} footnote, writeAgdaTo, startComment, stopComment, indent, dedent, citet, citeauthor, acknowledgements)
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
      chlipala_parametric_2008
      guillemette_type-preserving_2007
      guillemette_type-preserving_2008
      miller_proof_2003
      bird-paterson-99
     |]

title = «Parametric Nested Abstract Syntax»
  -- «A Classy Kind of Nested Abstract Syntax»
  -- «Implementing Names and Binders with Polymorphism»
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
when :: Bool → ParItemW → ParItemW
when True  x = x
when False _ = return ()

doComment :: ParItemW → ParItemW
doComment x = startComment >> x >> stopComment

commentWhen :: Bool → ParItemW → ParItemW
commentWhen True  x = doComment x
commentWhen False x = x

commentCode = commentWhen True
  
unpackTypeSig =  [agdaP|
  |unpack :: (∀ v. v → tm (w ▹ v)) → 
  |          (∀ v. v → tm (w ▹ v) → a) → a
  |]

q = p ""

body = {-slice .-} execWriter $ do -- {{{
  -- JP (when the rest is ready)
  notetodo «ACM classification (JP: no clue how it's done these days!)»
  section $ «Intro» `labeled` intro
  subsection $ «Example final»
  [agdaP|
  |{-# LANGUAGE RankNTypes, UnicodeSyntax, 
  |    TypeOperators, GADTs, MultiParamTypeClasses, 
  |    FlexibleInstances, UndecidableInstances, 
  |    IncoherentInstances, ScopedTypeVariables #-} 
  |import Prelude hiding (elem,any)
  |import Data.Foldable
  |import Data.Traversable
  |import Control.Applicative
  |import Data.List (nub,elemIndex)
  |]
  
  -- JP
  section $ «Overview» `labeled` overview
  -- subsection $ «DeBruijn Indices»
  p""«A common way to represent variables is by the number of variables bound 
      between the occurence of a given variable {|x|} and its declaration.»
      {- NP: try an alternative way of telling it, "counting the number of λs/binders one has to cross over to reach our λ/binder/binding-site -}
  notetodo «cite»
  p""«The main advantage of the technique two α-equivalent terms have exactly the same representation.»
  -- NP: I sort of object to this, namely this ok for closed terms, but I would say that comparing free variables with equality is not always the right
  -- choice. One could pick an alternative presentation by stressing that binders and bound names are canonically represented therefor simplifying
  -- α-equivalence.
  p""«A direct implementation of the technique may yield the following represtenation of untyped lambda terms:»
  [agdaP|
  |data Nat = Zero | Succ Nat
  |data TmDB where
  |  VarDB :: Nat → TmDB
  |  AppDB :: TmDB → TmDB → TmDB
  |  LamDB :: TmDB → TmDB
  |]
  p""«Using this representation, the representation of the constant function {|\x y → x|} is the following:»
  -- NP: \ vs λ
  [agdaP|
  |constDB :: TmDB
  |constDB = LamDB $ LamDB $ VarDB (Succ Zero)
  |]

  p""«However, such a direct implementation is naïve. It cannot statically distinguish bound and free variables.
      That is, a closed term has the same type as an open term.»

  -- subsection $ «Nested Abstract Syntax»
  p""«In Haskell, it is possible to remedy to this situation by “nested recursion”. 
      That is, one parameterises the type of terms by a type that can represent free variables.
      If the parameter is the empty type, terms are closed. If the parameter is the unit type, there is at most one free variable, etc.»
  -- NP: Term () can also holds closed terms.
  -- JP: What about Var () :: Term ()
  p""«This representation in known as Nested Abstract Syntax {cite[birdpaterson99]}»
  notetodo «cite»
  -- NP,TODO: 'type', 'class', 'instance', '::', '⇒' are not recognized as keywords
  -- NP: explain the meaning of Here and There
  [agdaP|
  |data a ▹ v = There a | Here v
  |type Succ a = a ▹ ()
  |              
  |data TmN a where
  |  VarN :: a → TmN a
  |  AppN :: TmN a → TmN a → TmN a
  |  LamN :: TmN (Succ a) → TmN a
  |]
  p""«The recursive case {|Lam|} changes the parameter type, increasing its cardinality by one.»

  p""«Using this representation, the representation of the constant function {|\x y → x|} is the following:»
  [agdaP|
  |constN :: TmN Zero
  |constN = LamN $ LamN $ VarN (There (Here ()))
  |]
  p ""«As promised, the type is explicit about {|constN|} being a close term: this 
       is ensured by using the empty type {|Zero|} as an argument to {|TmN|}.»
  [agdaP|
  |data Zero -- no constructor
  |magic :: Zero → a
  |magic _ = error "magic!"
  |]
  p "" «In passing, we remark that another valid type for closed terms is {|∀ a. TmN a|} 
       --- literally: the type of terms which have an unknown number of free variables.
       Indeed, because {|a|} is universally quantified, there is no way to construct an inhabitant of it; 
       one cannot possibly refer to any free variable.»
  p""«Another drawback of using de Bruijn indices is that it is easy to make a mistake
      when counting the number of binders between the declaration of a variable and its occurence.»

  -- subsection $ «Our stuff»
  p""«To address this issue, we propose the following representation:»
  notetodo «Frame this?»
  [agdaP|
  |data Tm w where
  |  Var :: w → Tm w
  |  App :: Tm w → Tm w → Tm w
  |  Lam :: (∀ v. v → Tm (w ▹ v)) → Tm w
  |]
  p""«That is, instead of adding a concrete unique type in the recursive parameter of {|Lam|}, 
      we quantify universally over a type variable {|v|} and add this type variable to the type of free variables.»
  p""«We also provide the sub-term with an arbitrary value of type {|v|}, to be used at occurences of the variable bound by {|Lam|}. »

  p""«The constant function is then represented as follows:»
  [agdaP|
  |constTm_ :: Tm Zero
  |constTm_ = Lam $ \x → Lam $ \y → Var (There (Here x))
  |]

  -- subsection $ «Safety»
  -- NP: one should explicitely say that we consider the bindings made by the
  -- host language to be our specification, therefore a mistake is to put the
  -- wrong number of There
  p""«Now, if one makes a mistake and forgets one {|There|} when typing the term, GHC rejects the definition.»
  commentCode [agdaP|
  |oops_ = Lam $ \x → Lam $ \y → Var (Here x) 
  |-- Couldn't match expected type `v1' 
  |--             with actual type `v'
  |]

  p""«In fact, the possibility of making a mistake is inexistant (if we ignore diverging terms). 
      Indeed, because the type {|v|} corresponding to a bound variable is universally quantified, 
      the only way to construct a value of its type is to use the variable bound by {|Lam|}.»
  p""«Conversely, in a closed context, if one considers the expression {|Var (f x)|}, only one possible value of {|f|} 
      is admissible. Indeed, any context, the type of variables is {|w = w0 ▹ v0 ▹ v1 ▹ ⋯ ▹ vn|} where {|v0|}, {|v1|}, … , {|vn|} 
      are all distinct and universally quantified, and none of them occurs as part of {|w0|}. 
      Hence, there is only one injection function from a given {|vi|} to {|w|}.»
  -- NP: unclear. One should make precise that x is comes from a "Lam $ \x ->" and that f is Thereⁿ (Here x)

  -- subsection $ «Auto-inject»
  p""«Knowing that the injection functions are uniquely determined by their type, 
      one may wish to infer them mechanically.
      Thanks the the powerful instance search mechanism implemented in GHC, this is feasible. 
      We can define a class {|v ∈ w|} capturing that {|v|} occurs as part of a context {|w|}:»
  [agdaP|
  |class v ∈ w where
  |  inj :: v → w
  |]  
  p""«We can then wrap the injection function and {|Var|} in a convenient package:»
  commentCode [agdaP|
  |var :: ∀ v w. (v ∈ w) ⇒ v → Tm w
  |var = Var . inj
  |]
  p""«and the constant function can be conveniently written:»
  [agdaP|
  |constTm :: Tm Zero
  |constTm = Lam $ \x → Lam $ \y → var x
  |]

  p""«Our term representation allows to construct terms with de Bruijn-indices, 
      combined with the safety and convenience of named variables. These advantages
      extend to the analysis and manipulation on terms.

   Indeed, because the representation contains both concrete indices and functions at
   bindinding sites, one can take advantage of either aspect when analysing and manipulating terms.
   »


  subsection $ «De Bruijn indices as names»
  -- our debruijn indices are typed with the context where they are valid.
  -- If that context is sufficently polymorphic, they can not be mistakenly used in a wrong context.
  -- a debruijn index in a given context is similar to a name.


  p "" «A common use case is that one wants to be able to check if an occurence of
        a variable is a reference to some previously bound variable. 
        With de Bruijn indices, one must (yet again) count the number of binders traversed 
        between the variable bindings and its potential occurences --- as error prone as it gets.
        Here as well, we can take advantage of polymorphism to ensure 
        that no mistake happens. We provide a combinator {|unpack|}, which transforms
        a binding structure
        (of type {|∀ v. v → Tm (w ▹ v)|}) into a sub-term with one more free variable 
        {|Tm (w ▹ v)|} and a value (called {|x|} below) of type {|v|}, where {|v|} is 
        bound existentially. We write the combinator in continuation-passing style
        in order to encode the existential as a universal quantifier:
        »
  unpackTypeSig
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
  |canEta :: Tm Zero → Bool
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
  |recognize :: Tm Zero → Bool
  |recognize t0 = case t0 of 
  |    Lam f → unpack f $ \x t1 → case t1 of
  |      Lam g → unpack g $ \y t2 → case t2 of
  |        App e1 (Var y) → y `isOccurenceOf` x && 
  |                         not (x `occursIn` e1)
  |        _ → False   
  |      _ → False   
  |    _ → False   
  |]

  p""«Again, even though our representation is a variant of de Bruijn indices, the use of polymorphism
      allows to refer to variables by name, while remaining safe.»

  -- NP
  section $ «Term Structure» `labeled` termStructure
  p "" $ «Laws»
  subsection $ «Contexts, inclusion and membership»
  [agdaP|
  |instance x ∈ (γ ▹ x) where
  |  inj = Here
  |  
  |instance (x ∈ γ) ⇒ x ∈ (γ ▹ y) where
  |  inj = There . inj
  |]

  [agdaP|
  |mapu :: (u → u') → (v → v') → (u ▹ v) → (u' ▹ v')
  |mapu f g (There x) = There (f x)
  |mapu f g (Here x) = Here (g x)
  |]

  [agdaP|
  |class a ⊆ b where
  |  injMany :: a → b
  |
  |instance a ⊆ a where injMany = id
  |
  |instance Zero ⊆ a where injMany = magic
  |
  |instance (γ ⊆ δ) ⇒ (γ ▹ v) ⊆ (δ ▹ v) where
  |  injMany = mapu injMany id
  |
  |instance (a ⊆ c) ⇒ a ⊆ (c ▹ b) where
  |  injMany = There . injMany
  |]

  p "" $ «free theorems»
  p "auto-weakening, type-class hack" mempty

  subsection $ «Renaming/Functor»
  [agdaP|
  |instance Functor Tm where
  |  fmap f (Var x) = Var (f x)
  |  fmap f (Lam g) = Lam (\x -> fmap (mapu f id) (g x))
  |  fmap f (App t u) = App (fmap f t) (fmap f u)
  |]

  [agdaP|
  |wk :: (Functor f, γ ⊆ δ) ⇒ f γ → f δ
  |wk = fmap injMany
  |]


  subsection $ «Algebraic Structure/Catamorphism»
  -- NP: this style (of using the variable parameter to represent intermediate
  -- results) could be detailed more here.
  q«
   One can take the example of a size function to illustrate this flexibility. A first way to compute the size of a term
   is to arrange to substitute each variable occurence by its size (the constant 1 for the purpose of this example).
   This can be realised by applying the constant 1 at every function argument of a Lam constructor. One then needs
   to adjust the type to forget the difference between the new variable and the others. The variable and application
   cases then offer no surprises. 
   »
  [agdaP|
  |size1 :: Tm Int → Int
  |size1 (Var x) = x
  |size1 (Lam g) = 1 + size1 (fmap untag (g 1))
  |size1 (App t u) = 1 + size1 t + size1 u
  |]

  [agdaP|
  |untag :: a ▹ a → a
  |untag (There x) = x 
  |untag (Here x) = x 
  |]

  p""«
   An other way to proceed is to simply pass a dummy object to the function arguments of Lam, and
   use only the de Bruijn index to compute results in the case of variables. Using this technique,
   the size computation looks as follows:
   »

  [agdaP|
  |size2 :: Tm a → Int
  |size2 (Var _) = 1
  |size2 (Lam g) = 1 + size2 (g ())
  |size2 (App t u) = 1 + size2 t + size2 u
  |]
  -- The size example is both a good showcase for the "g ()" style but
  -- also do not illustrate the "use only the de∼Bruijn index to compute results"

  p""«
   One may however chose to combine the two approaches. 
   This time we also assume an arbitrary environment 
   mapping free variables to a size. For each new variable,
   we pass the size that we want to assign to it to the binding function, and 
   we extend the environment to use that value on the new variable, or
   lookup in the old environment otherwise.
   »

  [agdaP|  
  |size :: (a → Int) → Tm a → Int
  |size f (Var x) = f x
  |size f (Lam g) = 1 + size (extend f) (g 1)
  |size f (App t u) = 1 + size f t + size f u
  |]
  [agdaP|  
  |extend g (Here a) = a
  |extend g (There b) = g b
  |]

  p""«This pattern can be generalized to any algebra over terms, yielding the following catamorphism over terms.
      Note that the algebra corresponds to the higher-order representation of lambda terms.»
  -- type TermAlgebra = TmF w a -> a
  [agdaP|
  |data TmAlg w a = TmAlg { pVar :: w → a
  |                       , pLam :: (a → a) → a
  |                       , pApp :: a → a → a }
  |
  |cata :: TmAlg w a → Tm w → a
  |cata φ s = case s of
  |   Var x   → pVar φ x
  |   Lam f   → pLam φ (cata (extendVar φ) . f)
  |   App t u → pApp φ (cata φ t) (cata φ u)
  |
  |extendVar :: TmAlg w a -> TmAlg (w ▹ a) a
  |extendVar φ = φ { pVar = extend (pVar φ) }
  |]

  subsection $ «Substitute/Monad»

  [agdaP|
  |instance Monad Tm where
  |  -- TODO ?
  |]

  [agdaP|
  |var :: (Monad tm, v ∈ a) ⇒ v → tm a
  |var = return . inj
  |]


  [agdaP|
  |subst :: Monad m ⇒ (v → m w) → m v → m w
  |subst = (=<<)
  |]

  [agdaP|
  |-- Kleisli arrows
  |type Kl m v w = v → m w
  |
  |-- '(▹ v)' is a functor in the category of Kleisli arrows
  |lift :: (Functor tm, Monad tm) ⇒ Kl tm a b → Kl tm (a ▹ v) (b ▹ v)
  |lift θ (There x) = wk (θ x)
  |lift θ (Here  x) = var x
  |]

  subsection $ «Packing and Unpacking Binders»

  p""«In order to examine the content of a term with another bound variable, 
      one must apply a concrete argument to the function of type {|∀v. v → Term (a ▹ v)|}.
      The type of that argument can be chosen freely --- that freedom is sometimes useful
      to write idiomatic code. One choice is 
      unit type and its single inhabitant {|()|}. This choice essentially reverts to using
      plain de_Bruijn indices, and it is often advisable to chose more specific types.
       
      In particular, a canonical choice is a maximally polymorphic type. This choice is
      captured in the {|unpack|} combinator.
      »
  commentCode unpackTypeSig


  [agdaP|
  |unpack b k = k fresh (b fresh)
  |fresh = error "accessing fresh variable!"
  |]

  p""«Since {|v|} is universally quantified in the continuation, the continuation cannot
  trigger the {|fresh|} exception omitting the use of {|seq|}.»


  p""«As we have seen in previous examples, the unpack combinator gives the possibility 
  to refer to a free variable by name, enabling for example to combare a variable
  occurrence with a free variable. Essentially, it offers a nominal interface to free variables:
  even though the running code will use de Bruijn indices, the programmer sees names; and
  the correspondence is implemented by the type system. 
  »

  p""«
  It is easy to invert the job of {|unpack|}. Indeed,
  given a term with a free variable (of type {|Tm (a ▹ v)|}) it is easy to
  reconstruct a binder: »
  [agdaP|
  |pack' :: Functor tm ⇒ tm (a ▹ v) → (∀ w. w → tm (a ▹ w))
  |pack' t = \y → fmap (mapu id (const y)) t
  |]
  p""«It is preferrable however, as in the variable case, to bring a named reference to the
  variable that one attempts to bind, in order not to rely on the index (zero in this case),
  but on a name, correctness.»
  [agdaP|
  |pack :: Functor tm ⇒ v' → tm (w ▹ v') → (∀ v. v → tm (w ▹ v))
  |pack x t = \y → fmap (mapu id (const y)) t
  |]

  p""«Hence, the pack combinator enables to give a nominal-style interface to binders:»
  [agdaP|
  |lam' :: v → Tm (w ▹ v) → Tm w
  |lam' x t = Lam (pack x t)
  |]
  
  subsection $ «Traversable»

  [agdaP|
  |instance Foldable Tm where
  |  foldMap = foldMapDefault
  |]

  [agdaP|
  |traverseu :: Functor f ⇒ (a → f a') → (b → f b') →
  |                              a ▹ b → f (a' ▹ b')
  |traverseu f _ (There x) = There <$> f x
  |traverseu _ g (Here x) = Here <$> g x
  |
  |instance Traversable Tm where
  |  traverse f (Var x) =
  |    Var <$> f x
  |  traverse f (App t u) =
  |    App <$> traverse f t <*> traverse f u
  |  traverse f (Lam g) = 
  |    unpack g $ \x b → 
  |      lam' x <$> traverse (traverseu f pure) b
  |]

  -- JP/NP
  section $ «Bigger Examples» `labeled` examples

  subsection $ «Free variables»
  q«The function which computes the frees variables of a term
    can be directly transcribed from its nominal-style specification,
    thanks to the {|unpack|} combinator.»
  [agdaP|
  |freeVars :: Tm w → [w]
  |freeVars (Var x) = [x]
  |freeVars (Lam f) = unpack f $ \ x t → 
  |   remove x (freeVars t)
  |freeVars (App f a) = freeVars f ++ freeVars a
  |]
  q«The function which removes a free variable from a list maps a context {|a ▹ v|}
    to a context {|a|}. The functon also takes a name for the variable being removed
    --- but it is used only for type-checking purposes. »
  [agdaP|
  |remove :: v -> [a ▹ v] → [a]
  |remove _ xs = [x | There x <- xs]
  |]

  subsection $ «Occurence Test»

  q«We first allow to indices to be compared, by providing the following two {|Eq|} instances:»
  [agdaP|
  |instance Eq Zero where
  |  (==) = magic
  |
  |-- NP: beware Here 1 == Here 2
  |instance Eq w ⇒ Eq (w ▹ v) where
  |  Here _ == Here _ = True
  |  There x == There y = x == y
  |  _ == _ = False
  |]
  q«Because the comparison can be performed only on indices with the same type,
    it is ensured by the type system that they refer to the same context, and hence are meaningful.

   These tests can be combined with the injection coming from the {|∈|} typeclass to test that
   a variable {|x|} from a context {|a|} is an occurence of a binder {|y|} with a type {|v|}:
   »
  [agdaP|
  |isOccurenceOf :: (Eq a, v ∈ a) ⇒ a → v → Bool
  |isOccurenceOf x y = x == inj y
  |]
  q«A test of occurence of any given binder can then be given the following expression»
  [agdaP|
  |occursIn :: (Eq a, v ∈ a) ⇒ v → Tm a → Bool
  |occursIn x t = any (`isOccurenceOf` x) (freeVars t)
  |]

  subsection $ «Test of α-equivalence»
  p""«
   Testing for α-equivalent terms is straightforward. Our representation contains de Bruijn indices, so
   we only need to ignore the higher-order aspect. This can be done by simply applying dummy elements
   at every binding site. Additionally, as a natural refinement over the mere α-equivalence test, we allow
   for an equality test to be supplied for free variables. This equality test is provided by an {|Eq|} instance:
   »

  [agdaP|
  |instance Eq w ⇒ Eq (Tm w) where
  |  Var x == Var x' = x == x'
  |  Lam g == Lam g' = g () == g' ()
  |  App t u == App t' u' = t == t' && u == u'        
  |]  

  -- NP: I would like to see my more general cmpTm

  subsection $ «Normalisation by evaluation»
  p""«One way to evaluate terms is to evaluate each subterm to normal form. If a redex is encountered, a hereditary substitution is 
      performed. This technique is known as normalisation by evaluation.»
  notetodo «cite»

  q«The substitution to apply merely embeds free variables into terms:»
  -- NP: unclear, we need to stress that we represent substitutions by
  -- functions from 'names' to 'terms'.
  [agdaP|
  |subst0 :: Monad tm ⇒ w ▹ tm w → tm w
  |subst0 (Here  x) = x
  |subst0 (There x) = return x
  |]

  q«We can then define (by mutual recursion) the application of normal forms to normal forms, and a substituter which hereditarily 
  uses it.»

  [agdaP|
  |app :: Tm w → Tm w → Tm w
  |app (Lam t) u = t u >>>= subst0
  |app t u = App t u
  |]

  -- NP: This one is the normal bind for Tm. No the app is the fancy one
  -- ok. Then we need to stress the relation with >>=.
  [agdaP|
  |(>>>=) :: Tm a -> (a -> Tm b) -> Tm b
  |Var x >>>= θ = θ x
  |Lam t >>>= θ = Lam (\x → t x >>>= lift θ)
  |App t u  >>>= θ = app (t >>>= θ) (u >>>= θ)
  |]

  q«The evaluator can then be written as a simple recursion on the term structure:»
  [agdaP|
  |eval :: Tm w → Tm w
  |eval (Var x) = Var x
  |eval (Lam t) = Lam (eval . t)
  |eval (App t u) = app (eval t) (eval u)
  |]


  subsection $ «Closure Conversion»
  p"" «Following {citet[guillemettetypepreserving2007]}»
  q«We first define the target language. It features variables and applications as usual.
    Most importantly, it has a constructor for {|Closure|}s, composed of a body and an 
    environment. The body of closures have exactly
    two free variables: {|vx|} for the parameter of the closure and {|venv|} for its environment.
    An environment will be realised by a {|Tuple|}. Inside the closure, elements of the environment
    will be accessed via their {|Index|} in the tuple. Finally, the {|LetOpen|} construction
    allows to access the components  of a closure (its first argument) in an arbitrary expression 
    (its second argument). This arbitrary expression has two extra free variables:
    {|vf|} for the code of the closure and {|venv|} for its environment.
    »
  [agdaP|
  |data LC w where
  |  VarC :: w → LC w
  |  AppC :: LC w → LC w → LC w
  |  Closure :: (∀ vx venv. vx → venv → 
  |           LC (Zero ▹ venv ▹ vx)) →
  |           LC w → 
  |           LC w
  |  Tuple :: [LC w] → LC w
  |  Index :: LC w → Int → LC w
  |  LetOpen :: LC a → 
  |             (∀ vf venv. vf → venv → 
  |              LC (a ▹ vf ▹ venv)) → LC a
  |]
  q«This representation is an instance of {|Functor|} and {|Monad|}, and the corresponding code
    offers no surprise.»
  [agdaP|
  |instance Functor LC where
  |instance Monad LC where
  |]

  q«We give a couple helper functions to construct applications and indexwise access in a tuple:»
  [agdaP|
  |($$) = AppC
  |infixl $$
  |
  |idx :: (v ∈ a) ⇒ v → Int → LC a
  |idx env = Index (var env)
  |]
  q«Closure conversion can then be implemented as a function from {|Tm|} to {|LC|}.
    The case of variables is trivial. For an abstraction, one must construct a closure,
    whose environment contains each of the free variables in the body. The application must
    open the closure, explicitly applying the argument and the environment.
  »
  notetodo «Include fig. 2 from {cite[guillemettetypepreserving2007]}»
  q«The implementation follows the pattern given by {citet[guillemettetypepreserving2007]}.
    We make one modification: in closure creation, instead of binding one by one the free variables {|yn|} in the body 
    to elements of the environment, we bind them all at once, using a substitution {|\z → idx env (indexOf z yn)|}.
    »
  [agdaP|
  |cc :: ∀ w. Eq w ⇒ Tm w → LC w  
  |cc (Var x) = VarC x
  |cc t0@(Lam f) = 
  |  let yn = nub $ freeVars t0
  |      bindAll :: ∀env. env -> w -> LC (Zero ▹ env)
  |      bindAll env = \z → idx env (indexOf z yn)
  |  in Closure (\x env → cc (f x) >>= 
  |                   (lift $ bindAll env))
  |          (Tuple $ map VarC yn)
  |cc (App e1 e2) = 
  |  LetOpen (cc e1)
  |          (\f env → var f $$ wk (cc e2) $$ var env)
  |]
  -- indexOf is not in the prelude?!
  [agdaP|
  |indexOf :: Eq a ⇒ a → [a] → Int
  |indexOf x [] = error "index not found"
  |indexOf x (y:ys) | x == y = 0
  |                 | otherwise = 1 + indexOf x ys
  |]
  q«
    Notably, {citeauthor[guillemettetypepreserving2007]} modify the function to 
    take an additional substitution argument, citing the difficulty to support
    a direct implementation with de Bruijn indices. We need not do any such thing: 
    modulo our slight modification,
    our representation is natural enough to support a direct implementation of the 
    algorithm.»

  subsection $ «CPS»
  p "" «Following {citet[chlipalaparametric2008]}»
  q «In the CPS representation, every intermediate result is named.»
  [agdaP|
  |data Tm' a where
  |  Halt' :: a → Tm' a
  |  App'  :: a → a → Tm' a
  |  Let   :: Primop a → (∀ w. w → Tm' (a ▹ w)) → Tm' a
  |
  |data Primop a where 
  |  Abs' :: (∀ w. w → Tm' (a ▹ w)) → Primop a
  |  Pair :: a → a → Primop a  -- Pair
  |  Π1   :: a → Primop a
  |  Π2   :: a → Primop a
  |]

  q«We will not use primops directly, but instead their composition with injection.»
  notetodo «Hide this.»
  [agdaP|
  |(<:>) :: (v ∈ a, v' ∈ a) ⇒ v → v' → Primop a 
  |x <:> y = Pair (inj x) (inj y)
  |
  |π1 :: (v ∈ a) ⇒ v → Primop a
  |π1 = Π1 . inj
  |
  |π2 :: (v ∈ a) ⇒ v → Primop a
  |π2 = Π2 . inj
  |
  |app' :: (v ∈ a, v' ∈ a) ⇒ v → v' → Tm' a 
  |app' x y = App' (inj x) (inj y)
  |
  |halt' :: (v ∈ a) ⇒ v → Tm' a 
  |halt' = Halt' . inj
  |  
  |]

  q«As {|Tm|}, {|Tm'|} enjoys a functor structure. »
  [agdaP|
  |instance Functor Tm' where 
  |  -- ...
  |]


  notetodo «Include fig. 6 from {cite[guillemettetypepreserving2008]} »
  [agdaP|
  |cps' :: Tm a -> (∀ v. v -> Tm' (a ▹ v))  → Tm' a
  |
  |cps'' :: (γ ⊆ a) => Tm γ -> (forall v. v -> Tm' (a ▹ v)) -> Tm' a
  |cps'' = cps' . wk
  |
  |cps' (Var v)     k = fmap untag (k v)
  |cps' (App e1 e2) k = cps' e1 $ \f -> 
  |                    cps'' e2 $ \x -> 
  |                    Let (Abs' (\x -> wk (k x))) $ \k' → 
  |                    Let (x <:> k') $ \p → 
  |                    app' f p
  |cps' (Lam e') k = 
  |  Let (Abs' $ \p → Let (π1 p) $ \x → 
  |                   Let (π2 p) $ \k' →
  |                   cps'' (e' x) $ \r → 
  |                   app' k' r)
  |      k
  |]

  notetodo «Include fig. 7 from chlipala»
  -- There does not seem to be a nice and natural instance of monad for 
  -- Tm' !
  [agdaP|
  |-- in e1, substitute Halt' by an arbitrary Tm' e2
  |letTerm :: ∀ v.
  |         Tm' v  →
  |         (∀ w. w  → Tm' (v ▹ w)) → 
  |         Tm' v 
  |letTerm (Halt' v)  e2 = fmap untag (e2 v)
  |letTerm (App' f x) e2 = App' f x
  |letTerm (Let p e') e2 = 
  |   Let (letPrim p e2) $ \x → 
  |   letTerm (e' x) (\y → wk (e2 y))
  |
  |letPrim :: Primop v → 
  |           (∀ w. w  → Tm' (v ▹ w)) → 
  |           Primop v 
  |letPrim (Abs' e) e2 = 
  |  Abs' $ \x → letTerm (e x) (\y → wk (e2 y))
  |letPrim (Pair x y) e2 = Pair x y
  |letPrim (Π1 y) e2 = Π1 y
  |letPrim (Π2 y) e2 = Π2 y  
  |]


  [agdaP|
  |cps :: Tm v → Tm' v
  |cps (Var v) = Halt' v
  |cps (App e1 e2) = 
  |  letTerm (cps e1) $ \ f → 
  |  letTerm (wk (cps e2)) $ \ x →
  |  Let (Abs' (\x → halt' x)) $ \k →
  |  Let (x <:> k) $ \p →
  |  app' f p 
  |                      
  |cps (Lam e') = 
  |  Let (Abs' $ \p → Let (π1 p) $ \x → 
  |                   Let (π2 p) $ \k →
  |                   letTerm (wk (cps (e' x))) $ \r → 
  |                   app' k r)
  |      (\x → halt' x)
  |]                         


  -- NP
  section $ «Comparisons» `labeled` comparison
  subsection $ «Fin»
  subsection $ «Maybe/Nested»
  p "" $ «Kmett's succ-less»
  subsection $ «PHOAS»
  q«We don't do typed representations (yet)»
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
  
  commentCode [agdaP|
  |lam :: ((∀ n. (Leq (S m) n ⇒ Fin n)) → Tm (S m))
  |        → Tm m
  |var :: Fin n → Tm n
  |]
  p "" «The above types also reveal somewhat less precise types that what we use.
        Notably, the {|Leq|} class captures only one aspect of context inclusion (captured by the class {|⊆|}
        in our development),
        namely that one context should be smaller than another.
        This means, for example, that the class constraint {|w ⊆ w'|} can be meaning fully resolved
        in more cases than {|Leq m n|}, in turn making functions such as {|wk|} more useful in practice.»

  q«Additionally, our {|unpack|} and {|pack|} combinators extends the technique to free variables.»

  subsection $ «NomPa (nominal fragment)»

  p""«{citet[pouillardunified2012]} describe an interface for names and binders which provides maximum safety.
      The library is writen in Agda, using dependent types. The interface makes use of an abstract notion 
      of {|World|}s (set of names), {|Binder|}s (name declaration), and {|Name|}s (the occurence of a name).

      A {|World|} can either be {|Empty|} or result of the addition of a {|Binder|} to an existing {|World|}, using the operator.
     »
  commentCode [agdaP|
  |-- Abstract interface
  |World :: *
  |Binder :: * 
  |Name :: World → *
  |Empty :: World 
  |(◅) :: Binder → World → World
  |]

  p""«
  A {|Name|} set is indexed by a {|World|}: this ties occurences to the context where they make sense.
  On top of these abstract notions, one can construct the following representation of terms (we use
  a Haskell-like syntax for dependent types, similar to that of {_Idris}):
  »
  
  commentCode [agdaP|
  |data Tm α where
  |  Var :: Name α → Tm α
  |  App :: Tm α → Tm α → Tm α
  |  Lam :: (b :: Binder) → Tm (b ◅ α) → Tm α
  |]

  q«The safety of the technique comes from the abstract character of the interface. If one
  were to give concrete definitions for {|Binder|}, {|World|} and their related operations,
  it becomes possible for user code to cheat the system.

  A drawback of the interface being abstract is that some subterms do not evaluate. 

  In contrast, our representation uses polymorphism to ensure safety. This means that
  there is one way to compromise safety, namely, by instanciating a type variable with
  a concrete type. We do not suffer the drawback abstraction: the representation is concrete,
  and concrete terms will always evaluate.
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

  p"" «{citet[guillemettetypepreserving2008]} change representation from HOAS to de Bruijn indices, arguing that HOAS is more suitable for
     CPS transform, while de Bruijn indices are more suitable for closure conversion.
     Our reprensentation supports a natural implementation of both transformations.
     »

  p "more remarks about safety" «
  We do not suffer from name-capture and complicated α-equivalence problems; but
  we can conveniently call variables by their name.
  »
  

  p "" «impredicativity»

  p "even more safety by no instanciation" «
  A careless user may nullify the safety of our system when instanciating a type variable 
  with a concrete type. This suggests the following type-system feature: a quantifier for 
  variables which can be instanciated only by other variables (introduced by the same quantifier).
  This is reminiscent of the nabla quantifier of {cite[millerproof2003]}.
  »
  notetodo «Can I type nabla?» -- TODO: *** Exception: myHchar: ∇

  p "performance!" « 
  Given such an extension, it would then become possible to improve the performance of term analysis. Indeed, 
  the only possible value applicable to a binder would be the {|fresh|} exception, and
  it becomes possible to implement it specially, by a null operation.
  »

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

  acknowledgements
     «We thank Emil Axelsson for discussions on name binding.»  

  notetodo «What about:»
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
