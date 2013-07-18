{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Scopes where

import Kit
import Paper.Keys

scopesDoc onlyInCode = do
  section $ «Scopes» `labeled` scopesSec

  p"flow"
   «Armed with an intuitive understanding of safe interfaces to
    manipulate de Bruijn indices, and the knowledge that one can
    abstract over any substitutive structure by using standard
    type-classes, we can recapitulate and succinctly describe the
    essence of our constructions.»

  notetodo «use a figure to collect some of the most crucial definitions»

  q«In Nested Abstract Syntax, a binder introducing one variable in
    scope, for an arbitrary term structure {|tm|} is represented as
    follows:»

  [haskellFP|
  |type SuccScope tm a = tm (Succ a)
  |]

  q«In essence, we propose two new, dual representations of binders,
    one based on universal quantification, the other one based on
    existential quantification.»

  onlyInCode [haskellFP|
  |type UnivScope f a = ∀ v. v → f (a ▹ v)
  |]
  commentCode [haskellFP|
  |type UnivScope  tm a = ∀ v.  v → tm (a ▹ v)
  |type ExistScope tm a = ∃ v. (v ,  tm (a ▹ v))
  |]

  q«The above syntax for existentials is not supported in {_Haskell},
    so we must use one of the lightweight encodings available. In
    the absence of view patterns, a CPS encoding is convenient for
    programming (so we used this so far), but a datatype representation
    is more convenient when dealing with scopes only:»

  [haskellFP|
  |data ExistScope tm a where
  |  E :: v → tm (a ▹ v) → ExistScope tm a
  |]

  q«As we have observed on a number of examples, these representations
    are dual from a usage perspective: the universal-based
    representation allows safe construction of terms, while the
    existential-based representation allows safe analysis of
    terms. Strictly speaking, safety holds only if one disregards
    non-termination and {|seq|}, but because the values of type {|v|}
    are never used for computation, mistakenly using a diverging term in
    place of a witness of variable name is far-fetched.»

  q«For the above reason, we do not commit to either side, and use the
    suitable representation on a case-by-case basis. This flexibility
    is possible because these scope representations ({|SuccScope|},
    {|UnivScope|} and {|ExistScope|}) are isomorphic. In the following
    we exhibit the conversion functions between {|SuccScope|} one side
    and either {|UnivScope|} or {|ExistScope|} on the other. We then
    prove that they form isomorphisms, assuming an idealized {_Haskell}
    lacking non-termination and {|seq|}.»

  -- NP: should we cite “Fast and loose reasoning is morally correct”

  subsection «{|UnivScope tm a ≅ SuccScope tm a|}»

  p"conversions"
   «The conversion functions witnessing the isomorphism are the
    following.»

  -- if you remove this newpage put back [haskellFP|
  newpage
  [haskellP|
  |succToUniv :: Functor tm ⇒
  |              SuccScope tm a → UnivScope tm a
  |succToUniv t = λ x → bimap id (const x) <$> t
  |]
  [haskellP|
  |univToSucc :: UnivScope tm a → SuccScope tm a
  |univToSucc f = f ()
  |]

  q«The {|univToSucc|} function has not been given a name in the
    previous sections, but was implicitly used in the definition
    of {|lam|}. This is the first occurrence of the {|succToUniv|}
    function.»

  q«We prove first that {|UnivScope|} is a proper representation
    of {|SuccScope|}, that is {|univToSucc . succToUniv ≡ id|}. This can
    be done by simple equational reasoning:»

  commentCode [haskellFP|
  |   univToSucc (succToUniv t)
  | ≡ {- by def -}
  |   univToSucc (λ x → bimap id (const x) <$> t)
  | ≡ {- by def -}
  |   bimap id (const ()) <$> t
  | ≡ {- by () having just one element -}
  |   bimap id id <$> t
  | ≡ {- by (bi)functor laws -}
  |   t
  |]

  q«The second property ({|succToUniv . univToSucc ≡ id|}) means that
    there is no ``junk'' in the representation: one cannot represent
    more terms in {|UnivScope|} than in {|SuccScope|}. It is more
    difficult to prove, as it relies on parametricity and in turn
    on the lack of junk (non-termination or {|seq|}) in the host
    language. Hence we need to use the free theorem for a value {|f|}
    of type {|UnivScope tm a|}. Transcoding {|UnivScope tm a|} to a
    relation by using Paterson's version {cite[fegarasrevisiting1996]}
    of the abstraction theorem {cite[reynolds83,bernardyproofs2012]},
    assuming additionally that {|tm|} is a functor. We obtain the
    following lemma:»

  commentCode [haskellFP|
  | ∀ v₁:*. ‼ ∀ v₂:*. ∀ v:v₁ → v₂.
  | ∀ x₁:v₁. ∀ x₂:*. v x₁ ≡ x₂.
  | ∀ g:(a ▹ v₁) → (a ▹ v₂).
  | (∀ y:v₁. New (v y) ≡ g (New y)) →
  | (∀ n:a. ‼ Old n     ≡ g (Old n)) →
  | f x₂ ≡ g <$> f x₁
  |]

  q«We can then specialize {|v₁|} and {|x₁|} to {|()|}, {|v|}
    to {|const x₂|}, and {|g|} to {|bimap id v|}. By definition, {|g|}
    satisfies the conditions of the lemma and we get:»

  commentCode [haskellFP|
  |f x ≡ bimap id (const x) <$> f ()
  |]

  q«We can then reason equationally:»

  commentCode [haskellFP|
  |   f
  | ≡ {- by the above -}
  |   λ x → bimap id (const x) <$> f ()
  | ≡ {- by def -}
  |   succToUniv (f ())
  | ≡ {- by def -}
  |   succToUniv (univToSucc f)
  |]

  subsection «{|ExistScope tm a ≅ SuccScope tm a|} »

  p"conversions"
   «The conversion functions witnessing the isomorphism are the
    following.»

  -- if you remove this newpage put back [haskellFP|
  newpage
  [haskellP|
  |succToExist :: SuccScope tm a → ExistScope tm a
  |succToExist = E ()
  |]
  [haskellP|
  |existToSucc :: Functor tm ⇒
  |               ExistScope tm a → SuccScope tm a
  |existToSucc (E _ t) = bimap id (const ()) <$> t
  |]

  q«One can recognise the functions {|pack|} and {|unpack|} as CPS
    versions of {|existToSucc|} and {|succToExist|}.»

  q«The proof of {|existToSucc . succToExist ≡ id|} (no junk) is nearly
    identical to the first proof about {|UnivScope|} and hence omitted.
    To prove {|succToExist . existToSucc ≡ id|}, we first remark that by
    definition:»

  commentCode [haskellFP|
  |succToExist (existToSucc (E y t)) ≡
  |  E () (fmap (bimap id (const ())) t)
  |]

  q«It remains to show that {|E y t|} is equivalent to the right-hand
    side of the above equation. To do so, we consider any observation
    function {|o|} of type {|∀ v. v → tm (a ▹ v) → K|} for some constant
    type {|K|}, and show that it returns the same result if applied
    to {|y|} and {|t|} or {|()|} and {|fmap (bimap id (const ()))
    t|}. This fact is a consequence of the free theorem associated
    with {|o|}:»

  commentCode [haskellFP|
  | ∀ v₁:*. ‼ ∀ v₂:*. ∀ v:v₁ → v₂.
  | ∀ x₁:v₁. ∀ x₂:*. v x₁ ≡ x₂.
  | ∀ t₁:tm (a ▹ v₁). ∀ t₂:tm (a ▹ v₂).
  | (∀ g:(a ▹ v₁) → (a ▹ v₂).
  |  (∀ y:v₁. New (v y) ≡ g (New y)) →
  |  (∀ n:a.  Old n     ≡ g (Old n)) →
  |  t₂ ≡ fmap g t₁) →
  | o x₂ t₂ ≡ o x₁ t₁
  |]

  q«Indeed, after specializing {|x₂|} to {|()|} and {|v|}
    to {|const ()|}, the last condition amounts
    to {|t₂ ≡ fmap (bimap id (const ())) t₁|}, and we get the desired
    result.»

  -- subsection «{|FunScope|}»
  --  «NP: this one comes from NbE»
  onlyInCode [haskellFP|
  |type FunScope tm a = ∀ b. (a → b) → tm b → tm b
  |
  |fmapFunScope :: (a → b) → FunScope tm a → FunScope tm b
  |fmapFunScope f g h x = g (h . f) x
  |
  |returnFunScope :: Monad tm ⇒ a → FunScope tm a
  |returnFunScope x f t = return (f x)
  |
  |bindSuccScope :: Monad tm ⇒ (a → SuccScope tm b) →
  |                   SuccScope tm a → SuccScope tm b
  |bindSuccScope f t = t >>= λ x → case x of
  |  Old y  → f y
  |  New () → return (New ())
  |
  |-- NP: I started this one by converting to
  |-- SuccScope, but so far I'm stuck here
  |bindFunScope :: Monad tm ⇒ (a → FunScope tm b) →
  |                  FunScope tm a → FunScope tm b
  |bindFunScope f t g u =
  |  funToUniv t u >>= λ x → case x of
  |    New y → y
  |    Old y → f y g u
  |
  |existToFun :: Monad tm ⇒ ExistScope tm a
  |                       → FunScope tm a
  |existToFun (E x t) f u = t >>= extend (x, u) (return . f)
  |
  |funToUniv :: Monad tm ⇒ FunScope tm a
  |                      → UnivScope tm a
  |funToUniv f = f Old . return . New
  |
  |-- funToSucc is a special case of funToUniv
  |funToSucc :: Monad tm ⇒ FunScope tm a
  |                      → SuccScope tm a
  |funToSucc f = funToUniv f ()
  |
  |-- succToFun is a special case of existToFun
  |succToFun :: Monad tm ⇒ SuccScope tm a
  |                      → FunScope tm a
  |succToFun = existToFun . E ()
  |]

  subsection $ «A Matter of Style» `labeled` styleSec

  q«We have seen that {|ExistScope|} is well-suited for term analysis,
    while {|UnivScope|} is well-suited for term construction. What
    about term {emph«transformations»}, which combine both aspects?
    In this case, one is free to choose either interface. This can be
    illustrated by showing both alternatives for the {|Lam|} case of the
    {|fmap|} function. (The {|App|} and {|Var|} cases are identical.)
    Because the second version is more concise, we prefer it in the
    upcoming examples, but the other choice is equally valid.»

  commentCode [haskellFP|
  |fmap' f (Lam b)
  |   = unpack b $ λ x t → lamP x (bimap f id <$> t)
  |fmap' f (Lam b)
  |   = lam (λ x → bimap f id <$> (b `atVar` x))
  |]

  q«When using {|succToUniv|}, the type of the second argument of
    {|succToUniv|} should always be a type variable in order to have
    maximally polymorphic contexts. To remind us of this requirement
    when writing code, we give the alias {|atVar|} for {|succToUniv|}.
    (Similarly, to guarantee safety, the first argument of {|pack|}
    (encapsulated here in {|lamP|}) must be maximally polymorphic.)»

  onlyInCode [haskellFP|
  |atVar = succToUniv
  |]

  subsection $ «Scope Representations and Term Representations»

  q«By using an interface such as ours, term representations can be
    made agnostic to the particular scope representation one might
    choose. In other words, if some interface appears well-suited
    to a given application domain, one might choose it as the scope
    representation in the implementation. Typically, this choice is be
    guided by performance considerations. Within this paper we favor
    code concision instead, and therefore in sec. {ref hereditarySec}
    we use {|ExistScope|}, and in sections {ref closureSec} and {ref
    cpsSec} we use {|UnivScope|}.»
