{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Related where

import Kit
import Paper.Keys

relatedDoc onlyInCode = do
  section $ «Related Work» `labeled` comparison

  q«Representing names and binders in a safe and convenient manner is a
    long-standing issue, with an extensive body of work devoted to it.
    A survey is far beyond the scope of this paper. Hence, we limit our
    comparison the work that we judge most relevant, or whose contrasts
    with our proposal is the most revealing.»

  q«However, we do not limit our comparison to interfaces for names and
    binders, but also look at terms representations. Indeed, we have
    noted in sec. {ref styleSec} that every term representation embodies
    an interface for binders.»

  --  «Tell how interfaces of locally-nameless (including Binders
  --  Unbound), α-caml, Fresh(OCaml)ML are all unsafe and require some
  --  side effects.»

  -- JP: I did not do this because all I know has been already said in
  -- the intro.

  subsection $ «{|Fin|}»

  p"Fin approach description"
   «Another approach already used and described by {citet fincites} is
    to index terms, names, etc. by a number, a bound. This bound is the
    maximum number of distinct free variables allowed in the value. This
    rule is enforced in two parts: variables have to be strictly lower
    than their bound, and the bound is incremented by one when crossing
    a name abstraction (a λ-abstraction for instance).»

  p"Fin type description"
   «The type {|Fin n|} is used for variables and represents natural
    numbers strictly lower than {|n|}. The name {|Fin n|} comes from the
    fact that it defines finite sets of size {|n|}.»

  p"Fin/Maybe connection"
   «We can draw a link with Nested Abstract Syntax. Indeed, as with the
    type {|Succ|} ({|(▹ ())|} or {|Maybe|}), the type {|Fin (suc n)|}
    has exactly one more element than the type {|Fin n|}. However, these
    approaches are not equivalent for at least two reasons. Nested
    Abstract Syntax can accept any type to represent variables. This
    makes the structure more like a container and this allows to exhibit
    the substitutive structure of terms as monads. The {|Fin|} approach
    has advantages as well: the representation is concrete and closer to
    the original approach of de Brujin. In particular the representation
    of free and bound variables is more regular, and it may be more
    amenable to the optimization of variables as machine integers.»

  {- There might even be ways to get a similar interface for Fin,
     it might get closer McBride approach, tough -}

  subsection $ «Higher-Order Abstract Syntax (HOAS)»

  q«A way to represent bindings of an object language is via the
    bindings of the host language. One naive translation of this idea
    yields the following term representation:»

  [haskellFP|
  |data TmH = LamH (TmH → TmH) | AppH TmH TmH
  |]

  q«An issue with this kind of representation is the presence of
    so-called “exotic terms”: a function of type {|TmH → TmH|} which
    performs pattern matching on its argument does not necessarily
    represent a term of the object language. A proper realization of the
    HOAS idea should only allow functions which use their argument for
    substitution.»

  q«It has been observed before that one can implement this restriction
    by using polymorphism. This observation also underlies the safety of
    our {|UnivScope|} representation.»

  q«Another disadvantage of HOAS is the negative occurrence
    of the recursive type, which makes it tricky to analyze
    terms {cite[washburnboxes2003]}.»


  subsection «Syntax for free»

  q«{citet[atkeyhoas09]} revisited the polymorphic encoding of the HOAS
    representation of the untyped lambda calculus. By constructing a
    model of System F's parametricity in {_Coq} he could formally prove
    that polymorphism rules out the exotic terms. Name abstractions,
    while represented by computational functions, cannot react to the
    shape of their argument and thus behave as substitutions. Here is
    this representation in {_Haskell}:»

  [haskellFP|
  |type TmF = ∀ a. ({-lam:-} (a → a) → a)
  |             → ({-app:-}  a → a  → a) → a
  |]

  q«And our familiar application function:»

  [haskellFP|
  |apTmF :: TmF
  |apTmF lam app = lam $ λ f → lam $ λ x → f `app` x
  |]

  p"catamorphism only & can't go back"
   «Being a polymorphic encoding, this technique is limited to analyze
    terms via folds (catamorphism). Indeed, there is no known safe
    way to convert a term of this polymorphic encoding to another
    safe representation of names. As Atkey shows, this conversion
    relies on the Kripke version of the parametricity result of this
    type. (At the moment, the attempts to integrate parametricity in
    a programming language only support non-Kripke versions {cite
    parametricityIntegrationCites}.)»

{- NP: what about putting this in the catamorphism section with a forward ref
  - to here?
  [haskellFP|
  |tmToTmF :: Tm Zero → TmF
  |tmToTmF t lam app = cata (TmAlg magic lam app)
  |]
  -}

  subsection «Parametric Higher-Order Abstract Syntax (PHOAS)» 

  q«{citet[chlipalaparametric2008]} describes a way to represent binders
    using polymorphism and functions. Using that technique, called
    Parametric Higher-Order Abstract Syntax (PHOAS), terms of the
    untyped λ-calculus are as represented follows:»

  [haskellFP|
  |data TmP a where
  |  VarP :: a → TmP a
  |  LamP :: (a → TmP a) → TmP a
  |  AppP :: TmP a → TmP a → TmP a
  |
  |type TmP' = ∀ a. TmP a
  |]

  q«Only universally quantified terms ({|TmP'|}) are guaranteed to
    correspond to terms of the λ-calculus.»

  q«The representation of binders used by Chlipala can be seen as
    a special version of {|UnivScope|}, where all variables are
    assigned the same type. This specialization has pros and cons. On
    the plus side, substitution is easier to implement with PHOAS:
    fresh variables do not need special treatment. The corresponding
    implementation of the monadic {|join|} is as follows:»

  onlyInCode [haskellP|
  |joinP :: TmP (TmP a) → TmP a
  |]
  [haskellFP|
  |joinP (VarP x)   = x
  |joinP (LamP f)   = LamP (λ x → joinP (f (VarP x)))
  |joinP (AppP t u) = AppP (joinP t) (joinP u)
  |]

  q«On the minus side, all the variables (bound and free) have the
    same representation. This means that they cannot be told apart
    within a term of type {|∀ a. TmP a|}. Additionally, once the type
    variable {|a|} is instantiated to a closed type, one cannot recover
    the polymorphic version. Furthermore while {|Tm Zero|} denotes a
    closed term, {|TmP Zero|} denotes a term {emph«without»} variables,
    hence no term at all. Therefore, whenever a user of PHOAS needs to
    perform some manipulation on terms, they must make an upfront choice
    of a particular instance for the parameter of {|TmP|} that supports
    all the required operations on free variables. This limitation is
    not good for modularity, and for code clarity in general. Another
    issue arises from the negative occurrence of the variable type.
    Indeed this makes the type {|TmP|} invariant: it cannot be made
    a {|Functor|} nor a {|Traversable|} and this not a proper {|Monad|}
    either.»

  q«The use-case of PHOAS presented by Chlipala is the representation
    of well-typed terms. That is, the parameter to {|TmP|} can be made
    a type-function, to capture the type associated with each variable.
    This is not our concern here, but we have no reason to believe that
    our technique cannot support this, beyond the lack of proper for
    type-level computation in {_Haskell} --- Chlipala uses {_Coq} for
    his development.»

  subsection $ «McBride's “Classy Hack”»

  -- the point of types isn’t the crap you’re not allowed to write,
  -- it’s the other crap you don’t want to bother figuring out.

  p""
   «{citet[mcbridenot2010]} has devised a set of combinators to
    construct λ-terms in de Brujin representation, with the ability to
    refer to bound variables by name. Terms constructed using McBride's
    technique are textually identical to terms constructed using ours.
    Another point of similarity is the use of instance search to recover
    the indices from a host-language variable name. A difference is that
    McBride integrates the injection in the abstraction constructor
    rather than the variable constructor. The type of the {|var|}
    combinator then becomes simpler, at the expense of {|lam|}:»

  commentCode [haskellFP|
  |lam :: ((∀ n. (Leq (S m) n ⇒ Fin n)) → Tm (S m))
  |       → Tm m
  |var :: Fin n → Tm n
  |]

  q«An advantage of McBride's interface is that it does not require the
    “incoherent instances” extension. »

  -- 'Ordered overlapping type family instances' will improve the
  -- situation for us.

  q«However, because McBride represents variables as {|Fin|}, the types
    of his combinators are less precise ours. Notably, the {|Leq|}
    class captures only one aspect of context inclusion (captured
    by the class {|⊆|} in our development), namely that one context
    should be smaller than another. This means, for example, that the
    class constraint {|a ⊆ b|} can be meaningfully resolved in more
    cases than {|Leq m n|}, in turn making functions such as {|wk|}
    more useful in practice. Additionally, our {|unpack|} and {|pack|}
    combinators extend the technique to term analysis and manipulation.»

  subsection $ «{_NomPa} (nominal fragment)» -- TODO: NP (revise -- optional eq. tests.) 

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
    ø      : World
    ¬Nameø : ¬ (Name ø)

    -- Names are comparable and exportable
    _==ᴺ_   : ∀ {α} (x y : Name α) → Bool

    -- The fresh-for relation
    _#_  : Binder → World → Set
    _#ø  : ∀ b → b # ø
    suc# : ∀ {α b} → b # α → (sucᴮ b) # (b ◅ α)

    Since we follow a de Bruijn style these are moot: type (:#) a b = (),
      const (), const ()

    -- inclusion between worlds
    _⊆_     : World → World → Set
    coerceᴺ  : ∀ {α β} → (α ⊆ β) → (Name α → Name β)
    ⊆-refl  : Reflexive _⊆_
    ⊆-trans : Transitive _⊆_
    ⊆-ø     : ∀ {α} → ø ⊆ α
    ⊆-◅     : ∀ {α β} b → α ⊆ β → (b ◅ α) ⊆ (b ◅ β)
    ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◅ α)

    In Haskell respectively (->), id, id, (.), magic, λf -> bimap f id,
      const Old.

  zeroᴮ : Binder
  zeroᴮ = Zero

  sucᴮ : Binder → Binder
  sucᴮ = Succ

* name abstraction
ƛ   : ∀ b → Tm (b ◅ α) → Tm α
-}

  p""
   «{citet[pouillardunified2012]} describe an interface for names and
    binders which provides maximum safety. The library {_NomPa} is
    written in {_Agda}, using dependent types. The interface makes use
    of a notion of {|World|}s (intuitively a set of names), {|Binder|}s
    (name declaration), and {|Name|}s (the occurrence of a name).

    A {|World|} can either be {|Empty|} (called {|ø|} in the
    library {_NomPa}) in or result of the addition of a {|Binder|} to an
    existing {|World|}, using the operator {|(◅)|}. The type {|Name|} is
    indexed by {|World|}s: this ties occurrences to the context where
    they make sense.»

  commentCode [haskellFP|
  |World :: *
  |Binder :: *
  |Empty :: World
  |(◅) :: Binder → World → World
  |Name :: World → *
  |]

  p""
   «On top of these abstract notions, one can construct the following
    representation of terms (we use a {_Haskell}-style syntax for
    dependent types, similar to that of {_Idris}):»

  commentCode [haskellFP|
  |data Tm α where
  |  Var :: Name α → Tm α
  |  App :: Tm α → Tm α → Tm α
  |  Lam :: (b :: Binder) → Tm (b ◅ α) → Tm α
  |]

  q«The safety of the technique comes from the abstract character of the
    interface. If one were to give concrete definitions for {|Binder|},
    {|World|} and their related operations, it would become possible for
    user code to cheat the system.

    A drawback of the interface being abstract is that some subterms
    do not evaluate. This point is of prime concern in the context of
    reasoning about programs involving binders.

    In contrast, our interfaces are concrete (code using it always
    evaluates), but it requires the user to choose the representation
    appropriate to the current use ({|SuccScope|}, {|UnivScope|} or
    {|ExistScope|}).»

  -- See NomPa.notes
