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
      implementationExtras
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
      washburn_boxes_2003
     |]

title = «Parametric Nested Abstract Syntax»
  -- «Names For Free --- Implementing Names and Binders with Polymorphism»
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

commentCode = doComment

unpackTypeSig =  [agdaFP|
  |unpack :: (∀ v. v → tm (a ▹ v)) →
  |          (∀ v. v → tm (a ▹ v) → b) → b
  |]

q = p ""

constTm =   
  [agdaFP|
  |constTm :: Tm Zero
  |constTm = Lam $ λ x → Lam $ λ y → var x
  |]

body = {-slice .-} execWriter $ do -- {{{
  notetodo «ACM classification (JP: no clue how it's done these days!)»
  
  notetodo «how to hide this stuff?»
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

  
-- JP (when the rest is ready)
  section $ «Intro» `labeled` intro
  p"What is it we offer?"«
    Nominal-style user code, without the problems of nominal representation (easy substitution).
    »
  commentCode constTm
  
  
  -- JP
  section $ «Overview» `labeled` overview
  -- subsection $ «DeBruijn Indices»

  p"de Bruijn indices"
   «A common way to represent variables is by the number of variables
    bound between the occurrence of a given variable {|x|} and its
    declaration.»

      {- NP: try an alternative way of telling it, "counting the number of λs/binders one has to cross over to reach our λ/binder/binding-site -}

  notetodo «cite»

  p"DB make α-eq easy"
   «The main advantage of the technique two α-equivalent terms have
    exactly the same representation.»

  -- NP: I sort of object to this, namely this ok for closed terms, but I would say that comparing free variables with equality is not always the right
  -- choice. One could pick an alternative presentation by stressing that binders and bound names are canonically represented therefor simplifying
  -- α-equivalence.

  p"Untyped DB terms"
   «A direct implementation of the technique may yield the following
    represtenation of untyped lambda terms:»

  [agdaFP|
  |data Nat = Zero | Succ Nat
  |data TmDB where
  |  VarDB :: Nat → TmDB
  |  AppDB :: TmDB → TmDB → TmDB
  |  LamDB :: TmDB → TmDB
  |]

  p""
   «Using this representation, the implementation of the constant
    function {|λ x y → x|} is the following:»

  [agdaFP|
  |constDB :: TmDB
  |constDB = LamDB $ LamDB $ VarDB (Succ Zero)
  |]

  p"no static scoping"
   «However, such a direct implementation is naïve. It cannot statically
    distinguish bound and free variables. That is, a closed term has the
    same type as an open term.»

  -- subsection $ «Nested Abstract Syntax»

  p"nested data types"
   «In Haskell, it is possible to remedy to this situation by “nested
    recursion”. That is, one parameterises the type of terms by a type
    that can represent free variables. If the parameter is the empty
    type, terms are closed. If the parameter is the unit type, there is
    at most one free variable, etc.»

  -- NP: we should stress that the parameter is the type of free-variables and
  -- therefor does not affect the representation of bound variables at all.
  -- NP: Term () can also holds closed terms.
  -- JP: What about Var () :: Term ()
  p"citation"
   «This representation in known as Nested Abstract
    Syntax {cite[birdpaterson99]}»

  notetodo «cite»

  -- NP,TODO: 'type', 'class', 'instance', '::', '⇒' are not recognized as keywords
  -- NP: explain the meaning of Here and There
  [agdaFP|
  |data a ▹ v = There a | Here v
  |
  |type Succ a = a ▹ ()
  |
  |data TmN a where
  |  VarN :: a → TmN a
  |  AppN :: TmN a → TmN a → TmN a
  |  LamN :: TmN (Succ a) → TmN a
  |]

  p"the type of Lam"
   «The recursive case {|Lam|} changes the parameter type, increasing its cardinality by one.»

  p"constN example"
   «Using this representation, the implementation of the constant
    function {|λ x y → x|} is the following:»

  [agdaFP|
  |constN :: TmN Zero
  |constN = LamN $ LamN $ VarN (There (Here ()))
  |]

  p"the type of constN"
   «As promised, the type is explicit about {|constN|} being a closed
    term: this is ensured by using the empty type {|Zero|} as an
    argument to {|TmN|}.»

  [agdaFP|
  |data Zero -- no constructor
  |magic :: Zero → a
  |magic _ = error "magic!"
  |]

  p"polymorphic terms are closed"
   «In passing, we remark that another valid type for closed terms
    is {|∀ a. TmN a|} --- literally: the type of terms which have any
    set of possible free variables. Indeed, because {|a|} is universally
    quantified, there is no way to construct an inhabitant of it; one
    cannot possibly refer to any free variable. In particular one can
    instantiate {|a|} to be the type {|Zero|}.»

  p"DB drawback"
   «The main drawback of using de Bruijn indices is that it is easy
    to make a mistake when counting the number of binders between the
    declaration of a variable and its occurrence.»

  -- subsection $ «Our stuff»

  p""
   «To address this issue, we propose the following representation:»

  notetodo «Frame this?»

  [agdaFP|
  |data Tm a where
  |  Var :: a → Tm a
  |  App :: Tm a → Tm a → Tm a
  |  Lam :: (∀ v. v → Tm (a ▹ v)) → Tm a
  |]

  p"explain ∀ v"
   «That is, instead of adding a concrete unique type in the recursive
    parameter of {|Lam|}, we quantify universally over a type
    variable {|v|} and add this type variable to the type of free
    variables.»

  p"explain v →"
   «We also provide the sub-term with an arbitrary value of type {|v|},
    to be used at occurrences of the variable bound by {|Lam|}.»

  -- NP: "provide the sub-term" is one side of the coin, the other side
  -- would be to say that a name abstraction receives a value of type v
  -- to be....

  p"const"
   «The constant function is then represented as follows:»

  [agdaFP|
  |constTm_ :: Tm Zero
  |constTm_ = Lam $ λ x → Lam $ λ y → 
  |             Var (There (Here x))
  |]

  -- subsection $ «Safety»

  p"host bindings are the spec"
   «In our approach, the binding structure, which can be identified as
    the {emph«specification»}, is written using the host language binders.
 
    At variable occurences, de Bruijn indices are still present in the
    form of the constructors {|Here|}
    and {|There|}, and are purely part of the
    {emph«implementation»}.»

  p"type-checking the number of There..."
   «Now, if one makes a mistake and forgets one {|There|} when typing
    the term, the Haskell type system rejects the definition.»

  commentCode [agdaFP|
  |oops_ = Lam $ λ x → Lam $ λ y → Var (Here x) 
  |-- Couldn't match expected type `v1' 
  |--             with actual type `v'
  |]

  p"no mistakes at all"
   «In fact, the possibility of making a mistake in the {emph«implementation»} is inexistant (if
    we ignore diverging terms). Indeed, because the type {|v|}
    corresponding to a bound variable is universally quantified, the
    only way to construct a value of its type is to use the variable
    bound by {|Lam|}.»

  p"unicity of injections"
   «Conversely, in a closed context, if one considers the
    expression {|Var (Thereⁿ (Here x))|}, only one possible value of
    {|n|} is admissible. Indeed, anywhere in the formation of a term, the type of variables
    is {|a = a0 ▹ v0 ▹ v1 ▹ ⋯ ▹ vn|} where {|v0|}, {|v1|}, … , {|vn|}
    are all distinct and universally quantified, and none of them occurs
    as part of {|a0|}. Hence, there is only one injection function from
    a given {|vi|} to {|a|}.»

  -- subsection $ «Auto-inject»

  p"auto-inject"
   «Knowing that the injection functions are uniquely determined by
    their type, one may wish to infer them mechanically. Thanks the
    the powerful instance search mechanism implemented in GHC, this
    is feasible. We can define a class {|v ∈ a|} capturing that {|v|}
    occurs as part of a context {|a|}:»

  [agdaFP|
  |class v ∈ a where
  |  inj :: v → a
  |]

  p"var"
   «We can then wrap the injection function and {|Var|} in a convenient
    package:»

  commentCode [agdaFP|
  |var :: ∀ v a. (v ∈ a) ⇒ v → Tm a
  |var = Var . inj
  |]

  p"constTm"
   «and the constant function can be conveniently written:»

  constTm

  p"pros"
   «Our term representation allows to construct terms with de Bruijn
    indices, combined with the safety and convenience of named
    variables. These advantages extend to the analysis and manipulation
    on terms. Indeed, because the representation contains both concrete
    indices and functions at binding sites, one can take advantage of
    either aspect when analysing and manipulating terms.»

  subsection $ «De Bruijn indices as names»
  -- our debruijn indices are typed with the context where they are valid.
  -- If that context is sufficently polymorphic, they can not be mistakenly used in a wrong context.
  -- a debruijn index in a given context is similar to a name.


  p"unpack"
   «A common use case is that one wants to be able to check if an
    occurrence of a variable is a reference to some previously bound
    variable. With de Bruijn indices, one must (yet again) count the
    number of binders traversed between the variable bindings and its
    potential occurrences --- as error prone as it gets. Here as well,
    we can take advantage of polymorphism to ensure that no mistake
    happens. We provide a combinator {|unpack|}, which transforms a
    binding structure (of type {|∀ v. v → Tm (a ▹ v)|}) into a sub-term
    with one more free variable {|Tm (a ▹ v)|} and a value (called {|x|}
    below) of type {|v|}, where {|v|} is bound existentially. We write
    the combinator in continuation-passing style in order to encode the
    existential as a universal quantifier:»

  unpackTypeSig

  p"why unpack works"
   «Because {|v|} is existentially bound and occurs only positively
    in {|Tm|}, {|x|} can never be used in a computation. It acts as a
    reference to a variable in a context, but in a way which is only
    accessible to the type-checker.

    For instance, when facing for example a term {|t|} of type
    {|Tm (a ▹ v ▹ v1 ▹ v2)|}, {|x|} refers to the third free variable
    in {|t|}.

    Using {|unpack|}, one can write a function recognising an
    eta-contractible term as follows: (Recall that an a eta-contractible
    term has the form {|λ x → e x|}, where {|x|} does not occur free
    in {|e|}.)»

  [agdaFP|
  |canEta :: Tm Zero → Bool
  |canEta (Lam e) = unpack e $ \x t → case t of
  |  App e1 (Var y) → y `isOccurenceOf` x && 
  |                   not (x `occursIn` e1)
  |  _ → False
  |canEta _ = False
  |]

  p"canEta"
   «In the above example, the functions {|isOccurenceOf|}
    and {|occursIn|} use the {|inj|} function to lift {|x|} to
    a reference in the right context before comparing it to the
    occurrences. The occurrence checks do not get more complicated
    in the presence of multiple binders. For example, the code which
    recognises the pattern {|λ x y → e x|} is as follows:»

  [agdaFP|
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

  p"slogan"
   «Again, even though our representation is a variant of de Bruijn
    indices, the use of polymorphism allows to refer to variables by
    name, using the instance search mechanism to fill in the
    details of implementation.»

  -- NP
  section $ «Term Structure» `labeled` termStructure

  p"intro functor"
   «As  with the  Nested Abstract  Syntax  approach the  type for  terms
    enjoys  interesting structures.  For instance  a general  “renaming”
    operation give  rises to  a {|Functor|} instance.»

  subsection $ «Renaming/Functor»

  p"describe Functor Tm"
   «The  “renaming” to  apply is  given as  a function {|f|}  from {|a|}
    to {|b|}  where {|a|} is  the type  of free  variables of  the input
    term ({|Tm a|})  and {|b|} is  the  type of  free  variables of  the
    “renamed”  term ({|Tm b|}).  The   renaming  operation  then  simply
    preserve  the structure  of the  input term,  using {|f|} to  rename
    free  variables and  upgrading {|f|} to {|(a ▹ v) → (b ▹ v)|}  using
    the  functoriality  of {|(▹ v)|}  with {|mapu f id|}.  Adapting  the
    function {|f|} is  not only  a type-checking matter  it is  meant to
    protect the bound name from being altered by {|f|}.»

  -- NP: potentially comment about 'g x'

  [agdaFP|
  |instance Functor Tm where
  |  fmap f (Var x)   = Var (f x)
  |  fmap f (Lam g)   = Lam (λ x → fmap (mapu f id) (g x))
  |  fmap f (App t u) = App (fmap f t) (fmap f u)
  |]

  p"functor laws"
   «Satisfying functor laws implies that the structure is preserved by a
    renaming.  Namely that  whatever  the function {|f|}  is doing,  the
    bound names are not going to change. As expected the laws are the following:»

  doComment
    [agdaFP|
    |fmap id ≡ id
    |fmap (f . g) ≡ fmap f . fmap g
    |]

  p"reading the laws"
   «Therefore the identity function corresponds to not renaming anything
    and compositions of renaming functions corresponds to two sequential
    renaming operations.»

  -- "proofs", appendix, long version, useless...
  -- using: fmap f (Lam g) = Lam (fmap (mapu f id) . g)
  doComment
    [agdaFP|
    |fmap id (Var x)
    |  = Var (id x) = Var x
    |
    |fmap id (Lam g)
    |  = Lam (fmap (mapu id id) . g)
    |  = Lam (fmap id . g)
    |  = Lam (id . g)
    |  = Lam g
    |
    |fmap (f . g) (Var x)
    |  = Var ((f . g) x)
    |  = Var (f (g x))
    |  = fmap f (Var (g x))
    |  = fmap f (fmap g (Var x))
    |
    |fmap (f . g) (Lam h)
    |  = Lam (fmap (mapu (f . g) id) . h)
    |  = Lam (fmap (mapu f id . mapu g id) . h)
    |  = Lam (fmap (mapu f id) . fmap (mapu g id) . h)
    |  = fmap f (Lam (fmap (mapu g id) . h))
    |  = fmap f (fmap g (Lam h))
    |]

  subsection $ «Substitute/Monad»

  [agdaFP|
  |instance Monad Tm where
  |  Var x   >>= θ = θ x
  |  Lam t   >>= θ = Lam (\x → t x >>= lift θ)
  |  App t u >>= θ = App (t >>= θ) (u >>= θ)
  |
  |  return = Var
  |]

  {-
  Var x   >>= Var = Var x
  Lam t   >>= Var = Lam (\x → t x >>= lift Var)
                  = Lam (\x → t x >>= Var)

  App t u >>= θ = App (t >>= θ) (u >>= θ)
  -}

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
  |lift θ (There x) = fmap There (θ x) -- wk (θ x)
  |lift θ (Here  x) = return (Here x)     -- var x
  |]
  -- JP: changed 'Var (Here x)' to 'return (Here x)'
  -- so that the code complies with the type signature given.
  -- 'lift' is used below for other monads. 

  {-
  lift Var x = Var x
  lift Var (There x) = wk (Var x) = fmap injMany (Var x) = Var (injMany x) =?= Var (There x)
  lift Var (Here  x) = var x = Var (inj x) =?= Var (Here x)
  -}

  {-
  lift return x = return x
  lift return (There x) = fmap There (return x) = return (There x)
  lift return (Here  x) = return (Here x)
  -}

  p "" $ «Laws»
  subsection $ «Contexts, inclusion and membership»
  [agdaFP|
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

  [agdaFP|
  |wk :: (Functor f, γ ⊆ δ) ⇒ f γ → f δ
  |wk = fmap injMany
  |]


  subsection $ «Traversable»

  p"explain traverse"
   «Functors enable to apply any pure function {|f :: a → b|} to the
    elements of a structure to get a new structure holding the images
    of {|f|}. Traversable structures enable to apply an effectful
    function {|f :: a → m b|} where {|m|} can be any {|Applicative|}
    functor. An {|Applicative|} functor is strictly more powerful
    than a {|Functor|} and strictly less powerful than a {|Monad|}.
    Any {|Monad|} is an {|Applicative|} and any {|Applicative|} is
    a {|Functor|}. To be traversed a structure only need an applicative
    and therefore will support monadic actions directly.»

  [agdaFP|
  |instance Traversable Tm where
  |  traverse f (Var x) =
  |    Var <$> f x
  |  traverse f (App t u) =
  |    App <$> traverse f t <*> traverse f u
  |  traverse f (Lam g) = 
  |    unpack g $ \x b →
  |      lam x <$> traverse (traverseu f pure) b
  |]

  p"explain traverseu"
   «In order to traverse name-abstractions, indices need to be traversed
    as well. The type {|(▹)|} is a bi-functor that is bi-traversable.
    The function {|traverseu|} is given two effectful functions, one for
    each case:»

  [agdaFP|
  |traverseu :: Functor f ⇒ (a → f a') → (b → f b') →
  |                              a ▹ b → f (a' ▹ b')
  |traverseu f _ (There x) = There <$> f x
  |traverseu _ g (Here x)  = Here  <$> g x
  |]

  p"explain foldMap"
   «Any traversable structure is also foldable. »

  [agdaFP|
  |instance Foldable Tm where
  |  foldMap = foldMapDefault
  |]

  subsection $ «Algebraic Structure/Catamorphism»
  -- NP: this style (of using the variable parameter to represent intermediate
  -- results) could be detailed more here.
  
  q«
   Our represtentation features three aspects which are usually kept separate. It
   has an higher-order aspect, a nominal aspect, and a de Bruijn indices aspect.
   Consequently, one can take advtantage of the benefits of each of there aspects when
   manipulating terms.
   
   One can take the example of a size function to illustrate this flexibility. 

   We first demonstrate the higher-order aspect. It is common in higher-order representations
   to supply a concrete value to substitute for a variable at each binding site. 
   Consequently we will assume that all free variables 
   are substituted for their size, and here the function will have type {|Tm Int → Int|}.

   In our {|size|} function, we will consider that each variable occurrence as the constant
   size 1 for the purpose of this example. 

   This is be realised by applying the constant 1 at every function argument of a {|Lam|} constructor. One then needs
   to adjust the type to forget the difference between the new variable and the others, by applying an {|untag|} function
   for every variable. The variable and application cases then offer no surprises. 
   »
  [agdaFP|
  |type Size = Int
  |]

  [agdaFP|
  |size1 :: Tm Size → Size
  |size1 (Var x) = x
  |size1 (Lam g) = 1 + size1 (fmap untag (g 1))
  |size1 (App t u) = 1 + size1 t + size1 u
  |]

  [agdaP|
  |untag :: a ▹ a → a
  |untag (There x) = x 
  |untag (Here x) = x 
  |]

  -- TODO: move in 1st position.
  p""«Second we demonstrate the nominal aspect.
   Each binder is simply {|unpack|}ed (ignoring the fresh variable obtained). Using this technique,
   the size computation looks as follows:
   »

  [agdaP|
  |size2 :: Tm a → Size
  |size2 (Var _) = 1
  |size2 (Lam g) = unpack g $ \x t -> 1 + size2 t
  |size2 (App t u) = 1 + size2 t + size2 u
  |]

  p""«Third, we demonstrate the de Bruijn index aspect. This time we assume an environment mapping 
      de Bruijn indices {|Nat|} to the  their value of the free variables they represent (a {|Size|} 
      in our case).
      In the input term, free variables
      are repenented merely by their index. 
      When going under a binder represented by a function {|g|}, we apply {|g|} to a dummy argument {|()|},
      then we convert the structure of free variables {|Nat :> ()|} into {|Nat|}, using the {|toNat|} function.
      Additionally the environment is extended with the expected value for the new variable.»

  [agdaP|
  |size3 :: (Nat → Size) → Tm Nat → Size
  |size3 f (Var x) = f x
  |size3 f (Lam g) = 1 + size3 f' (fmap toNat (g ()))
  |  where f' Zero = 1
  |        f' (Succ n) = f n
  |size3 f (App t u) = 1 + size3 f t + size f u
  |
  |toNat (Here ()) = Zero
  |toNat (There x) = Succ x
  |]

  p""«
  In our experience it is often convenient to combine the first and third approaches, as we
  illustrate below. 
  This time the environment maps an arbitrary context {|a|} to a value.
  For each new variable,
  we pass the size that we want to assign to it to the binding function, and 
  we extend the environment to use that value on the new variable, or
  lookup in the old environment otherwise.
  »

  [agdaFP|  
  |size :: (a → Size) → Tm a → Size
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
  [agdaFP|
  |data TmAlg w a = TmAlg { pVar :: w → a
  |                       , pLam :: (a → a) → a
  |                       , pApp :: a → a → a }
  |
  |cata :: TmAlg w a → Tm w → a
  |cata φ s = case s of
  |   Var x   → pVar φ x
  |   Lam f   → pLam φ (cata (extendAlg φ) . f)
  |   App t u → pApp φ (cata φ t) (cata φ u)
  |
  |extendAlg :: TmAlg w a -> TmAlg (w ▹ a) a
  |extendAlg φ = φ { pVar = extend (pVar φ) }
  |]

  subsection $ «Packing and Unpacking Binders»

  p""«In order to examine the content of a term with another bound variable, 
      one must apply a concrete argument to the function of type {|∀v. v → Term (a ▹ v)|}.
      The type of that argument can be chosen freely --- that freedom is sometimes useful
      to write idiomatic code. One choice is 
      unit type and its single inhabitant {|()|}. However this choice locally reverts to using
      plain Nested Abstract Syntax, and it is often advisable to chose more specific types.
      
      In particular, a canonical choice is a maximally polymorphic type. This choice is
      captured in the {|unpack|} combinator.
      »
      -- While I agree that using the unit type everywhere reverts to using
      -- Nested Abstract Syntax, the one time use of () is I think
      -- a good style since there is nothing to confuse about free variables
      -- since there is only one.

      -- In a total language, unpack would be
      -- defined as unpack b k = k () (b ()). Which essentially turns
      -- unpack b λ x t → E into let { x = () ; t = b () } in E.
      -- 
      -- However, a real implementation of the technique would need something like the
      -- nabla combinator, where unpack would essentially be provided natively.
      --
      -- I still like the pack/unpack mode a lot it shines well when multiple
      -- binders are opened at once.
  commentCode unpackTypeSig


  [agdaP|
  |unpack binder k = k fresh (binder fresh)
  |  where fresh = ()
  |]

  p""«The continuation {|k|}
  is oblivious to the 
  the monomorphic type used by the implementation of {|fresh|}: this is expressed by universally quantifing {|v|} in the type of the continuation {|k|}.

  In fact, thanks to parametricity, and because {|v|} occurs only positively in the arguments of {|k|},
  it is guaranteed that {|k|} cannot observe the implementation of {|fresh|} at all (except for the escape hatch of {|seq|}). 
  In particular one could even define {|fresh = undefined|}, and the code would continue to work.»

  p""«As we have seen in previous examples, the {|unpack|} combinator gives the possibility 
  to refer to a free variable by name, enabling for example to compare a variable
  occurrence with a free variable. Essentially, it offers a nominal interface to free variables:
  even though the running code will use de Bruijn indices, the programmer sees names; and
  the correspondence is enforced by the type system. 
  »

  p""«
  It is easy to invert the job of {|unpack|}. Indeed,
  given a term with a free variable (of type {|Tm (a ▹ v)|}) one can 
  reconstruct a binder as follows: »
  [agdaFP|
  |pack' :: Functor tm ⇒ tm (a ▹ v) →
  |                      (∀ w. w → tm (a ▹ w))
  |pack' t = \y → fmap (mapu id (const y)) t
  |]
  p""«It is preferrable however, as in the variable case, to request a named reference to the
  variable that one attempts to bind, in order not to rely on the index (zero in this case),
  but on a name, for correctness.»
  [agdaFP|
  |pack :: Functor tm ⇒ v' → tm (a ▹ v') → 
  |                     (∀ v. v → tm (a ▹ v))
  |pack x t = \y → fmap (mapu id (const y)) t
  |]

  p""«Hence, the {|pack|} combinator makes it possible to give a nominal-style 
      interface to binders. For example
      the {|lam|} constructor can be implemented as follows.»
  [agdaFP|
  |lam :: v → Tm (w ▹ v) → Tm w
  |lam x t = Lam (pack x t)
  |]

  q«It is even possible to make {|pack|} bind any known variable in
    a context, by using a typeclass similar to {|∈|}. The 
    implementation is straightforward and deferred to the appendix.»

  -- JP/NP
  section $ «Bigger Examples» `labeled` examples

  subsection $ «Free variables»

  p"explain freeVars"
   «The function which computes the free variables of a term can be
    directly transcribed from its nominal-style specification, thanks to
    the {|unpack|} combinator.»

  [agdaFP|
  |freeVars :: Tm w → [w]
  |freeVars (Var x) = [x]
  |freeVars (Lam b) = unpack b $ λ x t →
  |   remove x (freeVars t)
  |freeVars (App f a) = freeVars f ++ freeVars a
  |]

  p"explain remove"
   «The function which removes a free variable from a list maps a
    context {|a ▹ v|} to a context {|a|}. The function also takes a
    name for the variable being removed --- but it is used only for
    type-checking purposes.»

  {- NP:
  These throwaway arguments might be a bit worrisome. A more involved
  version would use a type known as Tagged

  data Tagged a b = Tagged b

  Or more specific to our usage

  data Binder v = TheBinder
  -- Iso to Tagged v ()

  unpack :: (∀ v. v → tm (w ▹ v)) →
            (∀ v. Binder v → tm (w ▹ v) → a) → a
  unpack b k = k TheBinder (b TheBinder)

  remove :: Binder v -> [a ▹ v] → [a]
  remove _ xs = [x | There x <- xs]

  ...

  in this case we should also have:

  (∀ v. Binder v → tm (w ▹ v))
  -}

  [agdaFP|
  |remove :: v -> [a ▹ v] → [a]
  |remove _ xs = [x | There x <- xs]
  |]

  p"freeVars is toList"
   «Thanks to terms being an instance of {|Traversable|} they are
    also {|Foldable|} meaning that we can combine all the elements
    of the structure (i.e. the free variables of the term) using any
    monoid. One particular monoid is the free monoid of lists. In
    short {|Data.Foldable.toList|} is computing the free variables of a
    term:»

  [agdaFP|
  |freeVars' :: Tm w → [w]
  |freeVars' = toList
  |]

  subsection $ «Occurence Test»

  q«We first allow to indices to be compared, by providing the following two {|Eq|} instances.
     First, the {|Zero|} type is vaccuously equipped with equality:»

  [agdaFP|
  |instance Eq Zero where
  |  (==) = magic
  |]
  q«Second, if two indices refer to the first variables they are equal; otherwise we recurse.
  We stress that this equality tests only the {emph«indices »}, not the contained in the type.
  For example {|Here 0 == Here 1|} is {|True|}»
  [agdaFP|
  |instance Eq w ⇒ Eq (w ▹ v) where
  |  Here  _ == Here  _ = True
  |  There x == There y = x == y
  |  _       == _       = False
  |]

  p"explain isOccurenceOf"
   «Because the comparisons can be performed only on indices sharing the
    same type, it is ensured by the type system that they refer to the
    same context, and hence are meaningful comparisons. These tests can
    be combined with the injection coming from the type class {|(∈)|} to
    test that a variable {|x|} from a context {|a|} is an occurrence of
    a binder {|y|} with a type {|v|}: »

  [agdaFP|
  |isOccurenceOf :: (Eq a, v ∈ a) ⇒ a → v → Bool
  |x `isOccurenceOf` y = x == inj y
  |]

  p"occursIn"
   «A test of occurrence of any given binder can then be given the following expression»

  [agdaFP|
  |occursIn :: (Eq a, v ∈ a) ⇒ v → Tm a → Bool
  |x `occursIn` t = any (`isOccurenceOf` x) (freeVars t)
  |-- OR:
  |-- x `occursIn` t = inj x `elem` freeVars t
  |-- OR: Using Data.Foldable.elem
  |-- x `occursIn` t = inj x `elem` t
  |]

  subsection $ «Test of α-equivalence»
  p""«
   Using our technique, two α-equivalent terms will have the same underlying representation. Despite this property,
   the Haskell compiler will refuse to generate an equality-test via a {|deriving Eq|} clause.
   This is caused by the presence of a function type inside the {|Tm|} type. Indeed, in general, extensional equality
   of functions is undecidable. Fortunately, equality for the parametric function type that we use {emph«is»} decidable.
   Indeed, thanks to parametricity, the functions cannot inspect their argument at all, and therefore it is 
   sufficient to test for equality at the unit type, done shown below:
  »
  [agdaFP|
  |instance Eq w ⇒ Eq (Tm w) where
  |  Var x == Var x' = x == x'
  |  Lam g == Lam g' = g () == g' ()
  |  App t u == App t' u' = t == t' && u == u'        
  |]
  -- NP: I would like to see my more general cmpTm

  q«However the application of {|()|} is somewhat worrisome, since we might now different 
    indices get the same {|()|} type. Even though the possibility of a mistake is very low
    in a direct equality test like the above, one might want to do more complex tests where the
    possibility of a mistake is real. In order to avoid this, one might want to use the {|unpack|}
    combinator as below:»

  commentCode [agdaFP|
  |  Lam g == Lam g' = unpack g $ \x t -> 
  |                    unpack g' $ \ x' t' -> 
  |                    t == t'
  |]
  q«This is however incorrect. Indeed, the fresh variables x and x' will receive incompatible type, and
    in turn t and t' do not have the same type and cannot be compared. Hence we must use another variant
    of the unpack combinator, which maintains the correspondance between contexts in two different terms.»

  [agdaFP|
  |unpack2 :: (forall v. v → f (a ▹ v)) -> 
  |           (forall v. v → g (a ▹ v)) -> 
  |            
  |           (forall v. v → f (a ▹ v) -> 
  |                          g (a ▹ v) -> b) ->
  |           b 
  |unpack2 f f' k = k fresh (f fresh) (f' fresh)          
  |  where fresh = error "cannot query fresh variables!"
  |]

  q«One can see {|unpack2|} as allocating a single fresh name which is shared in both {|t|} and {|t'|}.»

  commentCode [agdaFP|
  |  Lam g == Lam g' = unpack2 g g' $ \x t t' -> 
  |                    t == t'
  |]



  subsection $ «Normalisation by evaluation»
  p""«One way to evaluate terms is to evaluate each subterm to normal form. If a redex is encountered, a hereditary substitution is 
      performed. This technique is known as normalisation by evaluation.»
  notetodo «cite»

  q«The substitution to apply merely embeds free variables into terms:»
  -- NP: unclear, we need to stress that we represent substitutions by
  -- functions from 'names' to 'terms'.
  [agdaFP|
  |subst0 :: Monad tm ⇒ w ▹ tm w → tm w
  |subst0 (Here  x) = x
  |subst0 (There x) = return x
  |]

  q«We can then define (by mutual recursion) the application of normal forms to normal forms, and a substituter which hereditarily 
  uses it.»

  [agdaFP|
  |app :: Tm w → Tm w → Tm w
  |app (Lam t) u = t u >>>= subst0
  |app t u = App t u
  |]

  -- NP: This one is the normal bind for Tm. No the app is the fancy one
  -- ok. Then we need to stress the relation with >>=.
  [agdaFP|
  |(>>>=) :: Tm a -> (a -> Tm b) -> Tm b
  |Var x >>>= θ = θ x
  |Lam t >>>= θ = Lam (\x → t x >>>= lift θ)
  |App t u  >>>= θ = app (t >>>= θ) (u >>>= θ)
  |]

  q«The evaluator can then be written as a simple recursion on the term structure:»
  [agdaFP|
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
  [agdaFP|
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

  q«We give a couple helper functions to construct applications and indexwise access in a tuple:»
  [agdaFP|
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
  [agdaFP|
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
  [agdaFP|
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
  [agdaFP|
  |(<:>) :: (v ∈ a, v' ∈ a) ⇒ v → v' → Primop a 
  |π1 :: (v ∈ a) ⇒ v → Primop a
  |π2 :: (v ∈ a) ⇒ v → Primop a
  |app' :: (v ∈ a, v' ∈ a) ⇒ v → v' → Tm' a 
  |halt' :: (v ∈ a) ⇒ v → Tm' a 
  |]

  q«As {|Tm|}, {|Tm'|} enjoys a functor structure. »

  q«We implement a one-pass CPS transform (administrative redexes are not
  created). This is done by passing a continuation to the transformation.
  At the top-level the halting continuation is used.»

  [agdaFP|
  |cpsMain :: Tm a -> Tm' a
  |cpsMain x = cps x halt'
  |]

  q«The cases of {|App|} and {|Lam|} are standard. A direct encoding of 
  the definition, except for a couple occurrences of weakenings.
  Worth of mention: the continuation
  is bound as a {|Primop|} using the {|Abs'|} construction, before being 
  wrapped in a pair.»

  notetodo «Include fig. 6 from {cite[guillemettetypepreserving2008]} »
  [agdaFP|
  |cps :: Tm a -> (∀ v. v -> Tm' (a ▹ v)) → Tm' a
  |cps (App e1 e2) k = 
  |  cps e1 $ \f -> 
  |  cps (wk e2) $ \x -> 
  |  Let (Abs' (\x -> wk (k x))) $ \k' → 
  |  Let (x <:> k') $ \p → 
  |  app' f p
  |cps (Lam e')    k = 
  |  Let (Abs' $ \p → Let (π1 p) $ \x → 
  |                   Let (π2 p) $ \k' →
  |                   cps (wk (e' x)) $ \r → 
  |                   app' k' r)
  |      k
  |cps (Var v)     k = fmap untag (k v)
  |]

  q«In the variable case, we must pass the variable {|v|} to the continuation. We have:
  {|k v :: Tm' (a ▹ a)|}. To obtain a result of the right type it suffices to remove
  the extra tagging introduced by {|a ▹ a|} everywhere in the term, using {|fmap untag|}.»
  
  q«It is folklore that a CPS transformation is easier to implement with higher-order abstract 
  syntax {cite[guillemettetypepreserving2008,washburnboxes2003]}. Our representation of
  abstraction features a very limited form of higher-order representation. 
  (Namely, a quantification, over a universally quantified type.)
  However limited, this higher-order aspect is enough to allow an easy implementation of 
  the CPS transform.»


{-
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
-}
  -- NP
  section $ «Comparisons» `labeled` comparison
  subsection $ «Fin»
  subsection $ «Maybe/Nested»
  p "" $ «Kmett's succ-less»
  subsection $ «PHOAS»
  q«We don't do typed representations (yet)»
  subsection $ «HOAS»
  p "" «Functions should only be substitutions»
  q«{cite[washburnboxes2003]}»
  subsubsection $ «Concrete Terms»
  p "" «TmH → TmH | TmH × TmH»
  p "+" «Exotic terms»
  p "+" «Negative occurrences of the recursive type»
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

        Another difference is that McBride integrates the injection in the abstraction
        constructor rather than the variable constructor. The type of the {|var|} combinator becomes then
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

  q«Additionally, our {|unpack|} and {|pack|} combinators extend the technique to free variables.»

  subsection $ «NomPa (nominal fragment)»

{-
    -- minimal kit to define types
    World  : Set
    Name   : World → Set
    Binder : Set
    _◅_    : Binder → World → World

    -- An infinite set of binders
    zeroᴮ : Binder
    sucᴮ  : Binder → Binder

    -- Converting names and binders back and forth
    nameᴮ   : ∀ {α} b → Name (b ◅ α)
    binderᴺ : ∀ {α} → Name α → Binder

    -- There is no name in the empty world
    ø        : World
    ¬Nameø☐ : ¬ (Name ø)

    -- Names are comparable and exportable
    _==ᴺ_   : ∀ {α} (x y : Name α) → Bool 
    exportᴺ : ∀ {α b} → Name (b ◅ α) → Name (b ◅ ø) ⊎ Name α

    -- The fresh-for relation
    _#_  : Binder → World → Set
    _#ø  : ∀ b → b # ø
    suc# : ∀ {α b} → b # α → (sucᴮ b) # (b ◅ α) 

    -- inclusion between worlds
    _⊆_     : World → World → Set
    coerceᴺ  : ∀ {α β} → (α ⊆ β) → (Name α → Name β)
    ⊆-refl  : Reflexive _⊆_
    ⊆-trans : Transitive _⊆_
    ⊆-ø     : ∀ {α} → ø ⊆ α
    ⊆-◅     : ∀ {α β} b → α ⊆ β → (b ◅ α) ⊆ (b ◅ β) 
    ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◅ α) 

* exportᴺ? : ∀ {b α} → Name (b ◅ α) → Maybe (Name α)

  Celui la est ok est trivial
  exportᴺ? (here _)  = nothing
  exportᴺ? (there x) = just x

  nameᴮ : ∀ {α} b → Name (b ◅ α)
  nameᴮ = Here

  zeroᴮ : Binder
  zeroᴮ = Zero

  sucᴮ : Binder → Binder
  sucᴮ = Succ

  _#_ : Binder → World → Set
  b # α = ?

* name abstraction
ƛ   : ∀ b → Tm (b ◅ α) → Tm α
-}

  p""«{citet[pouillardunified2012]} describe an interface for names and binders which provides maximum safety.
      The library is writen in Agda, using dependent types. The interface makes use of an abstract notion 
      of {|World|}s (set of names), {|Binder|}s (name declaration), and {|Name|}s (the occurrence of a name).

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
  A {|Name|} set is indexed by a {|World|}: this ties occurrences to the context where they make sense.
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
  -- Actually this is independent of nabla.

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
  section $ «Implementation details» `labeled` implementationExtras
  subsection «CPS»
  
  [agdaP|
  |instance Functor Primop where  
  |  fmap f (Π1 x) = Π1 (f x)
  |  fmap f (Π2 x) = Π2 (f x)
  |  fmap f (Pair x y) = Pair (f x) (f y)
  |  fmap f (Abs' g) = Abs' (\x -> fmap (mapu f id) (g x))
  |  
  |instance Functor Tm' where 
  |  fmap f (Halt' x) = Halt' (f x)
  |  fmap f (App' x y) = App' (f x) (f y)
  |  fmap f (Let p g) = Let (fmap f p) (\x -> fmap (mapu f id) (g x))
  |]

  [agdaP|
  |x <:> y = Pair (inj x) (inj y)
  |π1 = Π1 . inj
  |π2 = Π2 . inj
  |app' x y = App' (inj x) (inj y)
  |halt' = Halt' . inj
  |]
  subsection «Closure Conversion»

  [agdaP|
  |instance Functor LC where
  |  fmap f t = t >>= return . f
  |
  |instance Monad LC where
  |  return = VarC
  |  VarC x >>= θ = θ x
  |  Closure c env >>= θ = Closure c (env >>= θ)
  |  LetOpen t g >>= θ = 
  |    LetOpen (t >>= θ) (\f env -> g f env >>= lift (lift θ))
  |  Tuple ts >>= θ = Tuple (map (>>= θ) ts)
  |  Index t i >>= θ = Index (t >>= θ) i
  |  AppC t u >>= θ = AppC (t >>= θ) (u >>= θ)
  |]

  section $ «Bind an arbitrary name»
  [agdaP|
  |pack' :: forall f v a b w. (Functor f, Insert v a b) =>
  |           v -> f b -> (w -> f (a ▹ w))
  |pack' _ t x = fmap (shuffle cx) t
  |  where cx :: v -> w
  |        cx _ = x
  |
  |class Insert v a b where    
  |  -- inserting 'v' in 'a' yields 'b'.
  |  shuffle :: (v -> w) -> b -> a ▹ w
  |
  |instance Insert v a (a ▹ v) where
  |  shuffle f (Here x) = Here (f x)
  |  shuffle f (There x) = There x
  |  
  |instance Insert v a b => Insert v (a ▹ v') (b ▹ v') where
  |  shuffle f (Here x) = There (Here x)
  |  shuffle f (There x) = case shuffle f x of
  |    Here y -> Here y
  |    There y -> There (There y)
  |]

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
