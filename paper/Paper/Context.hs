{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Context where

import Kit
import Paper.Keys
import Paper.Snippets

contextDoc onlyInCode = do
  section $ «Contexts» `labeled` contextSec

  p"flow" «Having introduced our interface informally, we now begin a
           systematic description of is realization and the concepts it builds upon.»
  

  p"flow, ▹"
   «We have seen that the type of free variables essentially describes
    the context where they are meaningful. A context can either be
    empty (and we represent it by the type {|Zero|}) or not (which we
    can represent by the type {|a ▹ v|}).»

  p"explain remove"
   «An important function of the {|v|} type variable is to make sure
    programmers refer to the variable they intend to. For example,
    consider the following function, which takes a list of (free)
    variables and removes one of them from the list. It takes a list
    of variables in the context {|a ▹ v|} and returns a list in the
    context {|a|}. For extra safety, it also takes the name of the
    variable being removed, which is used only for type-checking
    purposes.»

  -- (As for {|pack|}, {|remove|} can be generalized to use the {|Insert|})... However we have not seen ∈ yet, so this makes little sense.
  [haskellFP|
  |remove :: v → [a ▹ v] → [a]
  |remove _ xs = [x | Old x ← xs]
  |]

  p"explain freeVars"
   «The function which computes the list of occurrences of free variables in a term can
    be directly transcribed from its nominal-style definition, thanks
    to the {|unpack|} combinator.»

  [haskellFP|
  |freeVars :: Tm a → [a]
  |freeVars (Var x) = [x]
  |freeVars (Lam b) = unpack b $ λ x t →
  |   remove x (freeVars t)
  |freeVars (App f a) = freeVars f ++ freeVars a
  |]

  subsection $ «Names Are Polymorphic Indices»


  p"Eq Zero"
   «Checking whether two names are equal or not is necessary to implement a large 
    class of term manipulation functions.
    To implement comparison between names, we provide the following two {|Eq|} instances.
    First, the {|Zero|} type is vacuously equipped with equality:»

  [haskellFP|
  |instance Eq Zero where
  |  (==) = magic
  |
  |magic :: Zero → a
  |magic _ = error "impossible"
  |]

  p""
   «Second, if two indices refer to the first variable they are equal;
    otherwise we recurse. We stress that this equality inspects only the
    {emph«indices»}, not the values contained in the type. For
    example {|New 0 == New 1|} is {|True|}:»

  -- NP: TODO nbsp are messed up by the highlighter

  {-
  instance (Eq a, Eq v) ⇒ Eq (a ▹ v) where
    New x == New y = x == y
    Old x == Old y = x == y
    _     == _     = False

  instance Eq (Binder a) where
    _ == _ = True
  -}

  [haskellFP|
  |instance Eq a ⇒ Eq (a ▹ v) where
  |  New _ == New _ = True
  |  Old x == Old y = x == y
  |  _     == _     = False
  |]

  q«Comparing naked de Bruijn indices for equality is an error prone
    operation, because one index might be valid in a context different
    from the other, and thus an arbitrary adjustment might be required.
    With Nested Abstract Syntax, the situation improves: by requiring
    equality to be performed between indices of the same type, a whole
    class of errors are prevented by type-checking. Some mistakes are
    possible though: given an index of type {|a ▹ () ▹ ()|}, a swap
    of the last two variables might be the right thing to do, but
    one cannot decide if it is so from the types only. By making the
    contexts fully polymorphic as we propose, no mistake is possible.
    Hence the slogan: names are polymorphic indices.»

  q«Consequently, the derived equality instance of {|Tm|} gives
    α-equality, and is guaranteed safe in fully-polymorphic contexts.»

  onlyInCode [haskellFP|
  |deriving instance Eq a ⇒ Eq (Tm a)
  |]

  subsection «Membership»
  q«Given the above representation of contexts, we can implement
    the relation of context membership by a type class {|∈|}, whose
    sole method performs the injection from a member of the context to
    the full context. The relation is defined by two inference rules,
    corresponding to finding the variable in the first position of the
    context, or further away in it, with the necessary injections:»

  [haskellFP|
  |instance v ∈ (a ▹ v) where
  |  inj = New
  |
  |instance (v ∈ a) ⇒ v ∈ (a ▹ v') where
  |  inj = Old . inj
  |]

  p"incoherent instances"
   «The cognoscenti will recognize the two above instances as
    {emph«incoherent»}, that is, if {|v|} and {|v'|} were instantiated
    to the same type, both instances would apply, but the injections would be different. Fortunately,
    this incoherence never triggers as long as one keeps the contexts
    maximally polymorphic contexts: {|v|} and {|v'|} will always be
    different.»

  -- NP: maybe mention the fact that GHC let us do that

  p"inj enables var"
   «We have seen before that the overloading of the {|inj|} function
    in the type class {|∈|} allows to automatically convert a type-level
    reference to a term into a properly tagged de Bruijn index, namely
    the function {|var|}.»

  p"explain isOccurenceOf"
   «Conversely, one can implement occurrence-check by combining  {|inj|} with {|(==)|}:
    one first lifts the bound variable to the context of the chosen occurrence and
    then tests for equality.»

  [haskellFP|
  |isOccurenceOf :: (Eq a, v ∈ a) ⇒ a → v → Bool
  |x `isOccurenceOf` y = x == inj y
  |]

  p"occursIn"
   «One can test if a variable is fresh for a given term as follows:»
  -- We should not use Data.Foldable.elem here: we have not seen the
  -- Foldable instance yet.  At this point the cosmetic benefit is
  -- outweighed by the cost of the dangling (future) references.
  [haskellFP|
  |freshFor :: (Eq a, v ∈ a) ⇒ v → Tm a → Bool
  |x `freshFor` t = not (inj x `elem` freeVars t)
  |]


  subsection «Inclusion»
  p"context inclusion, ⊆"
   «Another useful relation is context inclusion between contexts, which we also
    represent by a type class, named {|⊆|}. The sole method of the
    typeclass is again an injection, from the small context to the
    bigger one. The main application of {|⊆|} is in term weakening,
    presented at the end of sec. {ref functorSec}.»
  [haskellFP|
  |class a ⊆ b where
  |  injMany :: a → b
  |]

  p"⊆ instances"
   «This time we have four instances: inclusion is reflexive; the empty
    context is the smallest one; adding a variable makes the context
    larger; and variable append {|(▹ v)|} is monotonic for inclusion.»

  [haskellFP|
  |instance a ⊆ a where injMany = id
  |
  |instance Zero ⊆ a where injMany = magic
  |
  |instance (a ⊆ b) ⇒ a ⊆ (b ▹ v) where
  |  injMany = Old . injMany
  |
  |instance (a ⊆ b) ⇒ (a ▹ v) ⊆ (b ▹ v) where
  |  injMany = mapOld injMany
  |]

  p"(▹) functoriality"
   «This last case uses the fact that {|(▹)|} is functorial in its first argument.»

