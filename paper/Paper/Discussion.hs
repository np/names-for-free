{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Discussion where

import Kit
import Paper.Keys

discussionDoc onlyInCode = do
  section $ «Discussion» `labeled` discussion

  subsection «Binding Many Variables» 
  q«
    In {|SuccScope|}, there is exactly one more free variable available in the sub-term.
    However, it might be useful to bind multiple names at once in a binder. This can 
    be done by using a type {|n|} of the appropriate cardinality instead of {|()|}.
    This technique has been used for example by {citet[boundkmett12]}.»
  [haskellFP|
  |type NScope n tm a = tm (a ▹ n)
  |]
  q«Adapting the idea to our framework would mean to quantify over a family of types,
    indexed by a type {|n|} of the appropriate cardinality:»
  commentCode [haskellFP|
  |type NUnivScope  n tm a = ∀v. (n → v) → tm (a ▹ v)
  |type NExistScope n tm a = ∃v.((n → v) , tm (a ▹ v))
  |]

  subsection $ «Delayed Substitutions»

  q«The main performance issue with de Brujn indices comes from the cost
    of importing terms into scopes without capture, which requires to
    increment free variables in the substituted term (see {|fmap Old|}
    in the definition of {|liftSubst|}). This transformation incurs not
    only a direct cost proportional to the size of terms, but also an
    indirect cost in the form of loss of sharing.»

  q«{_Citet[birdpaterson99]} propose a solution to this issue, which can
    be expressed simply as another implementation of binders, where free
    variables of the inner term stand for whole terms with one less free
    variable:»

  [haskellFP|
  |type DelayedScope tm a = tm (tm a ▹ ())
  |]

  q«This means that the parallel substitution for a term representation 
    based on {|DelayedScope|} does not require lifting of substitutions.»

  [haskellFP|
  |data TmD a where
  |  VarD :: a → TmD a
  |  LamD :: DelayedScope TmD a → TmD a
  |  AppD :: TmD a → TmD a → TmD a
  |]

  [haskellP|
  |instance Monad TmD where
  |  return = VarD
  |  VarD a   >>= θ = θ a
  |  AppD a b >>= θ = AppD (a >>= θ) (b >>= θ)
  |  LamD t   >>= θ = LamD (bimap (>>= θ) id <$> t)
  |]

  onlyInCode [haskellP|
  |instance Functor TmD where
  |  fmap = liftM
  |]

  q«Because idea of delayed substitutions is concerned with free
    variables, and the concepts we present here is concerned with bound
    variables, one can easily define scopes which are both delayed
    and safe. Hence the performance gain is compatible with our safe
    interface.»

  commentCode [haskellFP|
  |type UnivScope'  tm a = ∀v. (v → tm (tm a ▹ v))
  |type ExistScope' tm a = ∃v. (v ,  tm (tm a ▹ v))
  |]

{-
    Kmett's
    type {|Scope|} not only help improving performances but supports
    multiple binders and enjoys a structure of monad transformers.
    
JP: Why? and how does this fit with our interfaces?

-}


  subsection «Future Work: Improving Safety»
  q«As it stands our interface prevents mistakes in the manipulation of de Bruijn indices, but
    requires a collaboration from the user. 
    Indeed, a malicious user can instantiate {|v|} 
    to a monotype either in the analysis of
    {|∀ v. v → tm (a ▹ v)|} or in the construction of {|∃ v. (v, tm (a ▹ v))|}. This situation can be improved 
    by providing a quantifier which allows to substitute for type variables other type variables only.
    This
    quantifier can be understood as being at the same time existential and universal, 
    and hence is self dual.
    We use the notation {|∇|} (pronounced nabla) for it, due to the similarity with the quantifier
    of the same name introduced by {citet[millerproof2003]}.
    We would then have the following definitions, and safety could not be compromised. »

  commentCode [haskellFP|
   |type UnivScope  tm a = ∇ v.  v → tm (a ▹ v)
   |type ExistScope tm a = ∇ v. (v ,  tm (a ▹ v))
   |]
  q«
   These definitions would preclude using {|SuccScope|} as an implementation, 
   however this should not cause any issue: either of the above could be used directly
   as an implementation.
   Supporting our version of {|∇|} in a type-checker seems a rather modest extension,
   therefore we wish to investigate how some future version of GHC could support it.
   »

  subsection «Future Work: Improve Performance»
  -- NP: univToSucc is cheap as well no?
  q«An apparent issue with the presented conversion functions between
    {|UnivScope|} or {|ExistScope|} on one side and {|SuccScope|} on the
    other side is that all but {|succToExist|} cost a time 
    proportional to the size of the term converted. In the current state of affairs, we 
    might be able to use a system of rewrite rules, such as that implemented in GHC, to 
    eliminate the conversions to and from the safe interfaces. However, within
    a system which supports ∇-quantification, a better option offers itself:
    the machine-representation of the type {|v|} should be
    nil (nothing at all) if {|v|} is a ∇-bound variable; 
    therefore the machine-implementation of the conversions
    can be the identity.»

  subsection «Future Work: No Injections»

  p "getting rid of the injections by using a stronger type system" «
    We use the instance search of GHC in a very specific way: only to discover in injections.
    This suggests that a special-purpose type-system (featuring a form of subtyping)
    could be built to take care of those injections automatically.
    An obvious benefit would be some additional shortening of programs manipulating terms.
    Additionally, this simplification of programs would imply an
    even greater simplification of the proofs about them; indeed, a variation in complexity in
    an object usually yields a greater variation in complexity in proofs about it.
  »

  subsection «Conclusion»
  q«
  We have shown how to make de Bruijn indices safe, by typing them precisely with 
  the context where they make sense. Such precise contexts are obtained is by using (appropriately)
  either of the interfaces {|UnivScope|} or {|ExistScope|}. These two interfaces can 
  be seen as the both sides of the ∇ quantifier of {citet [millerproof2003]}. 
  Essentially, we have deconstructed that flavor of quantification over names, 
  and implemented it in {_Haskell}. The result is a safe method to manipulate names
  and binders, which is supported by today's Glasgow Haskell Compiler.»
  q«
  The method preserves the good properties of de Bruijn indices, while providing
  a convenient interface to program with multiple open binders. We have illustrated 
  these properties by exhibiting the implementation of a number of examples.
  »


  acknowledgments
   «We thank Emil Axelsson, Koen Claessen, Daniel Gustafsson and Patrik Jansson for
    useful feedback.»  -- In alphabetical order 
