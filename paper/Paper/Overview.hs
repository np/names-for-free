{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Overview where

import Kit
import Paper.Keys
import Paper.Snippets

overviewDoc onlyInCode = do
  section $ «Overview» `labeled` overview

  p"flow"
   «In this section we describe our interface, but before doing so we 
    describe a simple implementation which can support this interface.»

  subsection «de Bruijn Indices» -- {{{

  p"de Bruijn indices"
   «{_Citet[debruijnlambda1972]} proposed to represent an occurrence
    of some variable {|x|} by counting the number of binders that one
    has to cross between the occurrence and the binding site of {|x|}.
    A direct implementation of the idea may yield the following
    representation of untyped λ-terms:»

  [haskellFP|
  |data Nat = O | S Nat
  |data TmB where
  |  VarB :: Nat → TmB
  |  AppB :: TmB → TmB → TmB
  |  LamB :: TmB → TmB
  |]

  p"apB"
   «Using this representation, the implementation of the application
    function {|λ f x → f x|} is the following:»

  [haskellFP|
  |apB :: TmB
  |apB = LamB $ LamB $ VarB (S O) `AppB` VarB O
  |]

  p"no static scoping"
   «However, such a direct implementation is cumbersome and naïve. For
    instance it cannot statically distinguish bound and free variables.
    That is, a closed term has the same type as an open term.»

  paragraph «Nested Abstract Syntax»

  p"nested data types"
   «In functional programming languages such as {_Haskell}, it is
    possible to remedy to this situation by using nested data types
    and polymorphic recursion. That is, one parameterizes the type of
    terms by a type that can represent {emph«free»} variables. If the
    parameter is the empty type, terms are closed. If the parameter is
    the unit type, there is at most one free variable, etc.

    This representation is known as Nested Abstract Syntax {cite
    nestedcites}.»

  [haskellFP|
  |data Tm a where
  |  Var :: a → Tm a
  |  App :: Tm a → Tm a → Tm a
  |  Lam :: Tm (Succ a) → Tm a
  |]
  onlyInCode [haskellP|  deriving (Show)|]

  p"the type of Lam"
   «The recursive case {|Lam|} changes the type parameter, increasing
    its cardinality by one, since the body can refer to one more
    variable. Anticipating the amendments we propose, we define the
    type {|Succ a|} as a proper sum of {|a|} and the unit type {|()|}
    instead of {|Maybe a|} as customary. Because the sum is used in an
    asymmetric fashion (the left-hand-side corresponds to variables
    bound earlier and the right-hand-side to the freshly bound one),
    we give a special definition of sum written {|▹|}, whose syntax
    reflects the intended semantics.»

  [haskellFP|
  |type Succ a = a ▹ ()
  |
  |data a ▹ v = Old a | New v
  |
  |mapOld :: (a → a') → (a ▹ v) → (a' ▹ v)
  |mapOld f (Old x) = Old (f x)
  |mapOld _ (New x) = New x
  |
  |mapNew :: (v → v') → (a ▹ v) → (a ▹ v')
  |mapNew _ (Old x) = Old x
  |mapNew f (New x) = New (f x)
  |
  |untag :: a ▹ a → a
  |untag (Old x) = x
  |untag (New x) = x
  |]

  onlyInCode [haskellP|
  |bimap :: (a → a') → (v → v') →
  |         (a ▹ v) → (a' ▹ v')
  |bimap f _ (Old x) = Old (f x)
  |bimap _ g (New x) = New (g x)
  |]

--  |instance Bifunctor (▹) where
  onlyInCode [haskellP|deriving instance (Show a, Show b) ⇒ Show (a ▹ b)|]

  p"apNested example"
   «Using the {|Tm|} representation, the implementation of the
    application function {|λ f x → f x|} is the following:»

  [haskellFP|
  |apNested :: Tm Zero
  |apNested = Lam $ Lam $ Var (Old $ New ())
  |                 `App` Var (New ())
  |]

  p"the type of apNested"
   «As promised, the type is explicit about {|apNested|} being a closed
    term: this is ensured by using the empty type {|Zero|} as an
    argument to {|Tm|}.»

  [haskellFP|
  |data Zero -- no constructors
  |]

  p"polymorphic terms are closed"
   «In passing, we remark that another type which faithfully captures
    closed terms is {|∀ a. Tm a|} --- literally: the type of terms
    which are meaningful in any context. Indeed, because {|a|} is
    universally quantified, there is no way to construct an inhabitant
    of it; therefore one cannot possibly refer to any free variable. In
    particular one can instantiate {|a|} to be the type {|Zero|}.»

  p"de Bruijn drawback"
   «However the main drawback of using de Bruijn indices remains: one
    must still count the number of binders between the declaration of a
    variable and its occurrences.»

  -- }}}

  subsection «Referring to Bound Variables by Name» -- {{{

  p"flow"
   «To address the issues just touched upon, we propose to build
    λ-abstractions with a function called {|lam|}. What matters the most
    is its type:»

  [haskellFP|
  |lam :: (∀ v. v → Tm (a ▹ v)) → Tm a
  |lam f = Lam (f ())
  |]

  p"explain ∀ v, v →"
   «That is, instead of adding a concrete unique type (namely {|()|}) in
    the recursive parameter of {|Tm|}, we quantify universally over a
    type variable {|v|} and add this type variable to the type of free
    variables. The body of the lambda-abstraction receives an arbitrary
    value of type {|v|}, to be used at occurrences of the variable bound
    by {|lam|}.»

  p"const"
   «The application function is then built as follows:»

  [haskellFP|
  |apTm_ :: Tm Zero
  |apTm_ = lam $ λ f → lam $ λ x → Var (Old (New f))
  |                  ☐        `App` Var (New x)
  |]

  p"still the same elephant"
   «By unfolding the definition of {|lam|} in {|apTm_|} one recovers the
    definition of {|apNested|}.»

  paragraph «Safety»

  p"host bindings are the spec"
   «Using our approach, the binding structure, which can be identified
    as the {emph«specification»}, is written using the host language
    binders.

    However at variable occurrences, de Bruijn indices are still present
    in the form of the constructors {|New|} and {|Old|}, and are purely
    part of the {emph«implementation»}.»

  p"type-checking the number of Old..."
   «The type-checker then makes sure that the implementation matches the
    specification: for example if one now makes a mistake and forgets
    one {|Old|} when entering the term, the {_Haskell} type system
    rejects the definition.»

  commentCode [haskellFP|
  |oops_ = lam $ λ f → lam $ λ x → Var (New f)
  |                  ☐        `App` Var (New x)
  |-- Couldn't match expected type `v1'
  |--             with actual type `v'
  |]

  p"no mistakes at all"
   «In fact, if all variables are introduced with the {|lam|} combinator
    the possibility of making a mistake in the {emph«implementation»} is
    nonexistent, if we ignore obviously diverging terms. Indeed, because
    the type {|v|} corresponding to a bound variable is universally
    quantified, the only way to construct a value of its type is to
    use the variable bound by {|lam|}. (In {_Haskell} one can use a
    diverging program; however one has to make a conscious decision to
    produce a value of such an obviously empty type.)»

  p"unicity of injections"
   «In general, in a closed context, if one considers the
    expression {|Var ((Old)ⁿ (New x))|}, only one possible value
    of {|n|} is admissible. Indeed, anywhere in the formation of a term
    using {|lam|}, the type of variables is {|a = a₀ ▹ v₀ ▹ v₁ ▹ ⋯ ▹ vₙ|}
    where {|v₀|}, {|v₁|}, … , {|vₙ|} are all distinct and universally
    quantified, and none of them occurs as part of {|a₀|}. Hence, there
    is only one injection function from a given {|vᵢ|} to {|a|}.»

  paragraph «Auto-Inject»

  p"auto-inject"
   «Knowing that the injection functions are uniquely determined by
    their type, one may wish to infer them mechanically. Thanks the
    powerful instance search mechanism implemented in GHC, this is
    feasible. To this effect, we define a class {|v ∈ a|} capturing
    that {|v|} occurs as part of a context {|a|}:»

  [haskellFP|
  |class v ∈ a where
  |  inj :: v → a
  |]

  p"var"
   «We can then wrap the injection function and {|Var|} in a convenient
    package:»

  commentCode [haskellFP|
  |var :: ∀ v a. (v ∈ a) ⇒ v → Tm a
  |var = Var . inj
  |]

  p"apTm"
   «and the application function can be conveniently written:»

  apTm

  p"more intuitions"
   «In a nutshell, our de Bruijn indices are typed with the context
    where they are valid. If that context is sufficiently polymorphic,
    they can not be mistakenly used in a wrong context. Another
    intuition is that {|New|} and {|Old|} are building proofs of
    “context membership”. Thus, when a de Bruijn index is given a
    maximally polymorphic context, it is similar to a well-scoped name.»

  p"flow to next section"
   «So far, we have seen that by taking advantage of polymorphism,
    our interface allows to construct terms with de Bruijn indices,
    combined with the safety and convenience of named variables. In the
    next section we show how to use the same idea to provide the same
    advantages for the analysis and manipulation of terms.»

  -- }}}

  subsection «Referring to Free Variables by Name» -- {{{

  p"unpack"
   «Often, one wants to be able to check if an occurrence of a
    variable is a reference to some previously bound variable. With
    de Bruijn indices, one must (yet again) count the number of
    binders traversed between the variable bindings and its potential
    occurrences --- an error prone task. Here as well, we can take
    advantage of polymorphism to ensure that no mistake happens. We
    provide a combinator {|unpack|}, which hides the type of the newly
    bound variables (the type {|()|}) as an existentially quantified
    type {|v|}. The combinator {|unpack|} takes a binding structure
    (of type {|Tm (Succ a)|}) and gives a pair of a value {|x|} of
    type {|v|} and a sub-term of type {|Tm (a ▹ v)|}. Here we represent
    the existential using continuation-passing style instead of a
    data-type, as it appears more convenient to use this way. Because
    this combinator is not specific to our type {|Tm|} we generalize it
    to any type constructor {|f|}:»

  --    (See section TODO FORWARD REFERENCE for another solution
  --  based on view patterns.) 

  unpackCode

  -- NP: removed “occurs only positively in∼{|f|} (or∼{|Tm|})”
  -- since it is wrong if you can pick any f. Either we stick
  -- a Functor f instance or argue that this because of the lack
  -- of information of v.
  p"why unpack works"
   «Because {|v|} is existentially bound, {|x|} can never be used in a
    computation. It only acts as a reference to a variable in a context,
    in a way which is only accessible to the type-checker.

    For instance, when facing a term {|t|} of type
    {|Tm (a ▹ v₀ ▹ v₁ ▹ v)|}, {|x|} refers to the last introduced free
    variable in {|t|}.

    Using {|unpack|}, one can write a function which can recognize an
    eta-contractible term as follows: (Recall that an a eta-contractible
    term has the form {|λ x → e x|}, where {|x|} does not occur free
    in {|e|}.)»

  canEtaWithSig

  {-
   NP: Issue with unpack: it becomes hard to tell if a recursive function is
       total. Example:

       foo :: Tm a → ()
       foo (Lam e) = unpack e $ λ x t → foo t
       foo _       = ()

   As long as unpack is that simple, this might be one of those situations
   where we want to inline unpack. This new code is then termination checked
   and kept as the running program (let's not make the same mistakes as Coq).
  -}

  p"canEta"
   «In the above example, the two functions {|isOccurenceOf|}
    and {|freshFor|} use the {|inj|} function to lift {|x|} to
    a reference in the right context before comparing it to the
    occurrences. The calls to these functions do not get more
    complicated in the presence of multiple binders. For example, the
    code which recognizes the pattern {|λ x y → e x|} is as follows:»

  [haskellFP|
  |recognizeExample :: Tm Zero → Bool
  |recognizeExample t0 = case t0 of
  |    Lam f → unpack f $ λ x t1 → case t1 of
  |      Lam g → unpack g $ λ y t2 → case t2 of
  |        App e1 (Var z) → z `isOccurenceOf` x &&
  |                          x `freshFor` e1
  |                          y `freshFor` e1
  |        _ → False
  |      _ → False
  |    _ → False
  |]

  p"slogan"
   «Again, even though variables are represented by mere indices, the
    use of polymorphism allows the user to refer to them by name,
    using the instance search mechanism to fill in the details of
    implementation.»

  -- }}}

  {- subsection $ «Packing and Unpacking Binders» -- {{{

  p""
   «In order to examine the content of a term with another bound
    variable, one must apply a concrete argument to the function of type
    {|∀ v. v → Term (a ▹ v)|}. The type of that argument can be chosen
    freely --- that freedom is sometimes useful to write idiomatic code.
    One choice is unit type and its single inhabitant {|()|}. However
    this choice locally reverts to using plain Nested Abstract Syntax,
    and it is often advisable to chose a more specific type.

    In particular, a canonical choice is a maximally polymorphic type.
    This is the choice is made by using the {|unpack|} combinator.»

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
  commentCode unpackCode

  {-
  [haskellP|
  |unpack binder k = k fresh (binder fresh)
  |  where fresh = ()
  |]
  -}

  p""
   «The continuation {|k|} is oblivious to the monomorphic type used by
    the implementation of {|fresh|}: this is expressed by universally
    quantifing {|v|} in the type of the continuation {|k|}.

    In fact, thanks to parametricity, and because {|v|} occurs only
    positively in the arguments of {|k|}, it is guaranteed that {|k|}
    cannot observe the implementation of {|fresh|} at all (except for
    the escape hatch of {|seq|}). In particular one could even define
    {|fresh = undefined|}, and the code would continue to work.»

  p""
   «As we have seen in previous examples, the {|unpack|} combinator
    gives the possibility to refer to a free variable by name, enabling
    for example to compare a variable occurrence with a free variable.
    Essentially, it offers a nominal interface to free variables: even
    though the running code will use de Bruijn indices, the programmer
    sees names; and the correspondence is enforced by the type system.»
  -} -- }}}

  paragraph «Pack» -- {{{

  p"pack"
   «It is easy to invert the job of {|unpack|}. Indeed, given a
    value {|x|} of type {|v|} and a term of type {|Tm (a ▹ v)|} one can
    reconstruct a binder as follows: »

  [haskellFP|
  |pack :: Functor tm ⇒ v → tm (a ▹ v) → tm (Succ a)
  |pack x = fmap (mapNew (const ()))
  |]

  q«(The {|Functor|} constraint is harmless, as we will see in sec.
    {ref termStructure}.) As we can see, the value {|x|} is not used
    by pack. However it statically helps as a specification of the
    user intention: it makes sure the programmer relies on host-level
    variable names, and not indices.»

  -- TODO
  q«A production-quality version of {|pack|} would allow to bind any
    free variable. Writing the constraint {|Insert v a b|} to mean
    that by removing the variable {|v|} from the context {|b|} one
    obtains {|a|}, then a generic {|pack|} would have the following
    type:»

  [haskellFP|
  |packGen :: ∀ f v a b w. (Functor f, Insert v a b) ⇒
  |           v → f b → (w → f (a ▹ w))
  |]

  q«The implementation of {|packGen|} and {|Insert|} is a
    straightforward extension of {|inj|} and {|(∈)|}, but it does not
    fit here, so we defer it to the appendix.»

  p"lamP"
   «In sum, the {|pack|} combinator makes it possible to give a
    nominal-style interface to binders. For example an alternative way
    to build the {|Lam|} constructor is the following:»

  [haskellFP|
  |lamP :: v → Tm (a ▹ v) → Tm a
  |lamP x t = Lam (pack x t)
  |]

  -- }}}
