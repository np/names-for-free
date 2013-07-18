{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.TermStructure where

import Kit
import Paper.Keys

termStructureDoc = do
  section $ «Term Structure» `labeled` termStructure

  p"motivation"
   «It is well-known that every term representation parameterized
    on the type of free variables should exhibit monadic structure,
    with substitution corresponding to the binding operator {cite
    nestedcites}. That is, a {|Monad tm|} constraint means that a
    term representation {|tm|} is stable under substitution. In this
    section we review this structure, as well as other standard
    related structures on terms. These structures are perhaps easier
    to implement directly on a concrete term representation, rather
    than our interface. However, we give an implementation solely based
    on it, to demonstrate that it is complete with respect to these
    structures. By doing so, we also illustrate how to work with our
    interface in practice.»

  subsection $ «Renaming and Functors» `labeled` functorSec

  p"intro functor"
   «The first, perhaps simplest, property of terms is that free
    variables can be renamed. This property is captured by
    the {|Functor|} structure.»

  p"describe Functor Tm"
   «The “renaming” to apply is given as a function {|f|} from {|a|}
    to {|b|} where {|a|} is the type of free variables of the input
    term ({|Tm a|}) and {|b|} is the type of free variables of the
    “renamed” term ({|Tm b|}). While the function {|f|} should be injective
    to be considered a renaming, the functor instance
    works well for any function {|f|}. The renaming operation then
    simply preserves the structure of the input term. At occurrence
    sites it uses {|f|} to rename free variables. At binding sites,
    {|f|} is upgraded from {|(a → b)|} to {|(a ▹ v → b ▹ v)|} using
    the functoriality of {|(▹ v)|} with {|bimap f id|}. Adapting the
    function {|f|} is necessary to protect the bound name from being
    altered by {|f|}, and thanks to our use of polymorphism, the
    type-checker ensures that we make no mistake in doing so.»

  [haskellFP|
  |instance Functor Tm where
  |  fmap f (Var x)   = Var (f x)
  |  fmap f (Lam b)   = unpack b $ λ x t →
  |                       lamP x $ fmap (bimap f id) t
  |  fmap f (App t u) = App (fmap f t) (fmap f u)
  |]

  p"functor laws"
   «As usual satisfying functor laws implies that the structure is
    preserved by the functor action ({|fmap|}). The type for terms being
    a functor therefore means that applying a renaming is going to only
    affect the free variables and leave the structure untouched. That is,
    whatever the function {|f|} is doing, the bound names are not
    changing. The {|Functor|} laws are the following:»

  doComment
    [haskellFP|
    |fmap id ≡ id
    |fmap (f . g) ≡ fmap f . fmap g
    |]

  p"reading the laws"
   «In terms of renaming, they mean that the identity function corresponds
    to not renaming anything
    and compositions of renaming functions corresponds to two sequential
    renaming operations.»

  q«Assuming only a functor structure, it is possible to write useful
    functions on terms which involve only renaming. A couple of examples
    follow.»

  q«First, let us assume an equality test on free variables. 
    We can then write a function
    {|rename (x,y) t|} which replaces free occurrences of {|x|} in {|t|}
    by {|y|} and {|swap (x,y) t|} which exchanges free occurrences
    of {|x|} and {|y|} in {|t|}.»

  [haskellFP|
  |rename0 :: Eq a ⇒ (a, a) → a → a
  |rename0 (x,y) z | z == x    = y
  |                | otherwise = z
  |
  |rename :: (Functor f, Eq a) ⇒ (a, a) → f a → f a
  |rename = fmap . rename0
  |]

  [haskellP|
  |swap0 :: Eq a ⇒ (a, a) → a → a
  |swap0 (x,y) z | z == y    = x
  |              | z == x    = y
  |              | otherwise = z
  |
  |swap :: (Functor f, Eq a) ⇒ (a, a) → f a → f a
  |swap = fmap . swap0
  |]

    {-
  -- "proofs", appendix, long version, useless...
  -- using: fmap f (Lam g) = Lam (fmap (bimap f id) . g)
  doComment
    [haskellFP|
    |fmap id (Var x)
    |  = Var (id x) = Var x
    |
    |fmap id (Lam g)
    |  = Lam (fmap (bimap id id) . g)
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
    |  = Lam (fmap (bimap (f . g) id) . h)
    |  = Lam (fmap (bimap f id . bimap g id) . h)
    |  = Lam (fmap (bimap f id) . fmap (bimap g id) . h)
    |  = fmap f (Lam (fmap (bimap g id) . h))
    |  = fmap f (fmap g (Lam h))
    |]
  -}

  p"auto-weakening"
   «Second, let us assume two arguments {|a|} and {|b|} related by the
    type class {|⊆|}. Thus we have {|injMany|} of type {|a → b|}, which
    can be seen as a renaming of free variables via the functorial
    structure of terms. By applying {|fmap|} to it, one obtains
    an arbitrary weakening from the context {|a|} to the bigger
    context {|b|}.»

  [haskellFP|
  |wk :: (Functor f, a ⊆ b) ⇒ f a → f b
  |wk = fmap injMany
  |]

  q«Again, this arbitrary weakening function relieves the programmer from
    tediously counting indices and constructing an appropriate renaming function. We
    demonstrate this feature in sec. {ref examples}.»

  subsection $ «Substitution and Monads» `labeled` monadSec

  q«Another useful property of terms is that they can be substituted for free variables in
    other terms. This property is captured algebraically by asserting
    that terms form a {|Monad|}, where {|return|} is the variable
    constructor and {|>>=|} acts as parallel substitution. Indeed, one
    can see a substitution from a context {|a|} to a context {|b|} as
    mapping from {|a|} to {|Tm b|}, (technically a morphism in the associated Kleisli
    category) and {|(>>=)|} applies a substitution everywhere in a term.»

  q«The definition of the {|Monad|} instance is straightforward for
    variable and application, and we isolate the handling of binders in
    the {|(>>>=)|} function.»

  [haskellFP|
  |instance Monad Tm where
  |  return = Var
  |  Var x   >>= θ = θ x
  |  Lam s   >>= θ = Lam (s >>>= θ)
  |  App t u >>= θ = App (t >>= θ) (u >>= θ)
  |]

  q«At binding sites, one needs to lift the substitution so that it does not
    act on the newly bound variables, a behavior isolated in the helper {|>>>=|}. As for the {|Functor|} instance,
    the type system guarantees that no mistake is made. Perhaps
    noteworthy is that this operation is independent of the concrete
    term structure: we only “rename” with {|fmap|} and inject variables
    with {|return|}.»

  -- TODO we under use the monadic structure of tm∘(▹v)
  [haskellFP|
  |liftSubst :: (Functor tm, Monad tm) ⇒
  |          v → (a → tm b) → (a ▹ v) → tm (b ▹ v)
  |liftSubst _ θ (Old x) = fmap Old (θ x)
  |liftSubst _ θ (New x) = return (New x)
  |]

{-
The job of >>>= is basically:
(>>>=) :: (a → tm b) → s tm a → s tm b
introduce θ : a → tm b
          x : s tm a

apply θ inside x (using appropriate higher-order fmap) and get
          y : s tm (tm b)

then the crucial point is to lift out tm:

          z : s (tm ∘ tm) b

then apply join inside the structure (using the other higher-order fmap)

          w : s tm b
-}

  q«Substitution under a binder {|(>>>=)|} is then the wrapping
    of {|liftSubst|} between {|unpack|} and {|pack|}. It is uniform as
    well, and thus can be reused for every structure with binders.»

  -- TODO NP: SuccScope/UnivScope/... are monad transformers

  [haskellFP|
  |(>>>=) :: (Functor tm, Monad tm) ⇒
  |          tm (Succ a) → (a → tm b) → tm (Succ b)
  |s >>>= θ = unpack s $ λ x t →
  |             pack x (t >>= liftSubst x θ)
  |]

  p"laws"
   «For terms, the meaning of the monad laws can be interpreted as follows.
    The associativity law ensures that applying a composition of
    substitutions is equivalent to sequentially applying them, while the
    identity laws ensure that variables act indeed as such.»


  q«We can write useful functions for terms based only on the {|Monad|} structure. 
    For example, given the membership ({|∈|}), one can provide the a
    generic combinator to reference to a variable within any term structure:»

  [haskellFP|
  |var :: (Monad tm, v ∈ a) ⇒ v → tm a
  |var = return . inj
  |]

  q«One can also substitute an arbitrary variable:»

  [haskellFP|
  |substitute :: (Monad tm, Eq a, v ∈ a) ⇒
  |              v → tm a → tm a → tm a
  |substitute x t u = u >>= λ y →
  |     if y `isOccurenceOf` x then t else return y
  |]

  -- NP: I changed the names again, I agree that this often the function
  -- we should be using, however this is not what is expected to correspond
  -- to one substitution as in t[x≔u]
  q«One might however also want to remove the substituted
    variable from the context while performing the substitution:»
  [haskellFP|
  |substituteOut :: Monad tm ⇒
  |                 v → tm a → tm (a ▹ v) → tm a
  |substituteOut x t u = u >>= λ y → case y of
  |     New _ → t
  |     Old x → return x
  |]


  {-
  lift Var x = Var x
  lift Var (Old x) = wk (Var x) = fmap injMany (Var x) = Var (injMany x) =?= Var (Old x)
  lift Var (New  x) = var x = Var (inj x) =?= Var (New x)
  -}

  {-
  lift return x = return x
  lift return (Old x) = fmap Old (return x) = return (Old x)
  lift return (New  x) = return (New x)
  -}

  subsection «Traversable»

  p"explain traverse"
   «Functors enable to apply any pure function {|f :: a → b|} to the
    elements of a structure to get a new structure holding the images
    of {|f|}. Traversable structures enable to apply an effectful
    function {|f :: a → m b|} where {|m|} can be any {|Applicative|}
    functor. An {|Applicative|} functor is strictly more powerful
    than a {|Functor|} and strictly less powerful than a {|Monad|}.
    Any {|Monad|} is an {|Applicative|} and any {|Applicative|}
    is a {|Functor|}. To be traversed a structure only needs
    an applicative and therefore support monadic actions
    directly {cite[mcbrideapplicative2007]}.»

  [haskellFP|
  |instance Traversable Tm where
  |  traverse f (Var x)   = Var <$> f x
  |  traverse f (App t u) =
  |    App <$> traverse f t <*> traverse f u
  |  traverse f (Lam t)   =
  |    unpack t $ λ x b →
  |      lamP x <$> traverse (bitraverse f pure) b
  |]

  p"explain bitraverse"
   «In order to traverse name abstractions, indices need to be traversed
    as well. The type {|(▹)|} is a bi-functor and is bi-traversable.
    The function {|bitraverse|} is given two effectful functions, one for
    each case:»

  [haskellFP|
  |bitraverse :: Functor f ⇒ (a     → f a')
  |                        → (b     → f b')
  |                        → (a ▹ b → f (a' ▹ b'))
  |bitraverse f _ (Old x) = Old <$> f x
  |bitraverse _ g (New x) = New <$> g x
  |]

  q«An example of a useful effect to apply is throwing an exception,
    implemented for example as the {|Maybe|} monad. If a term has no
    free variable, then it can be converted from the type {|Tm a|}
    to {|Tm Zero|} (or equivalently {|∀ b. Tm b|}), but this requires a dynamic
    check. It may seem like a complicated implementation is necessary,
    but in fact it is a direct application of the {|traverse|}
    function.»

  [haskellFP|
  |closed :: Traversable tm ⇒ tm a → Maybe (tm b)
  |closed = traverse (const Nothing)
  |]

  p"freeVars is toList"
   «Thanks to terms being an instance of {|Traversable|} they are
    also {|Foldable|} meaning that we can combine all the elements of
    the structure (i.e. the occurrences of free variables in the term)
    using any {|Monoid|}. One particular monoid is the free monoid of
    lists. Consequently, {|Data.Foldable.toList|} is computing the
    free variables of a term and {|Data.Foldable.elem|} can be used to
    build {|freshFor|}:»

  [haskellFP|
  |freeVars' :: Tm a → [a]
  |freeVars' = toList
  |
  |freshFor' :: (Eq a, v ∈ a) ⇒ v → Tm a → Bool
  |x `freshFor'` t = not (inj x `elem` t)
  |]

{- NP: cut off-topic?
  -- TODO flow
  p""
   «New the function {|size|} takes as an argument how to assign
    a size to each free variable (the type {|a|}). An alternative
    presentation would instead require a term whose variables are
    directly of type {|Size|}. One can recover this alternative by
    passing the identity function as first argument. However the other
    way around requires to traverse the term.»

  -- TODO maybe too much
  [haskellFP|
  |type S f b = forall a. (a -> b) -> f a -> b
  |type T f b = f b -> b
  |
  |to :: S f b -> T f b
  |to s = s id
  |
  |from :: Functor f =>  T f b -> S f b
  |from t f = t . fmap f
  |]

could we get some fusion?

s f . fmap g
==
s (f . g)

-}
