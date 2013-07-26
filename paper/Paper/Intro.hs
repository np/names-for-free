{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Intro where

import Kit
import Paper.Snippets
import Paper.Keys

introDoc = do
  section $ «Introduction» `labeled` intro

  p"the line of work where we belong"
   «One of the main application areas of functional programming
    languages such as {_Haskell} is programming language technology.
    In particular, {_Haskell} programmers often find themselves
    manipulating data structures representing some higher-order object
    languages, featuring binders and names.»

  -- NP: not sure about «higher-order object language»

  p"identifying the gap"
   «Yet, the most commonly used representations for names and binders
    yield code which is difficult to read, or error-prone to write
    and maintain. The techniques in question are often referred as
    “nominal”, “de Bruijn indices” and “Higher-Order Abstract Syntax
    (HOAS)”.»

  -- NP: We can make this better.
  p"Nominal pros&cons"
   «In the nominal approach, one typically uses some atomic type to
    represent names. Because a name is simply referred to the atom
    representing it, the nominal style is natural. The main issues
    with this technique are that variables must sometimes be renamed
    in order to avoid name capture (that is, if a binder refers to an
    already used name, variables might end up referring to the wrong
    binder). The need for renaming demands a way to generate fresh
    atoms. This side effect can be resolved with a supply for unique
    atoms or using an abstraction such as a monad but is disturbing
    if one wishes to write functional code. Additionally, nominal
    representations are not canonical. (For instance, two α-equivalent
    representations of the same term such as {|λx.x|} and {|λy.y|}
    may be different). Hence special care has to be taken to prevent
    user code to violate the abstraction barrier. Furthermore fresh
    name generation is an observable effect breaking referential
    transparency ({|fresh x in x ≢ fresh x in x|}). For instance a
    function generating fresh names and not properly using them to close
    abstractions becomes impure.»

  -- NP: Note that in a safe interface for binders the supply does not
  -- have to be threaded, only passed downward and can be represented
  -- by a single number that we know all the numbers above are fresh
  -- names.

  p"de Bruijn pros&cons"
   «To avoid the problem of name capture, one can represent names
    canonically, for example by the number of binders, typically λ,
    to cross between an occurrence and its binding site (a de Bruijn
    index). This has the added benefit of making α-equivalent terms
    syntactically equal. In practice however, this representation makes
    it hard to manipulate terms: instead of calling things by name,
    programmers have to rely on their arithmetic abilities, which turns
    out to be error-prone. As soon as one has to deal with more than
    just a couple open bindings, it becomes easy to make mistakes.»

  p"HOAS"
   «Finally, one can use the binders of the host language (in our case
    {_Haskell}) to represent binders of the object language. This
    technique (called HOAS) does not suffer from name-capture problems
    nor does it involve arithmetic. However the presence of functions in
    the term representation mean that it is difficult to manipulate, and
    it may contain values which do not represent any term.»

  {- NP: the HOAS point of view is that this is more an issue of using Haskell
     function space that is improper for this situation. -}

  p"contribution"
   «The contribution of this paper is a new programming interface for
    binders, which provides the ability to write terms in a natural
    style close to concrete syntax. We can for example build the
    application function of the untyped λ-calculus as follows:»

  commentCode apTm

  q«and we are able to test if a term is eta-contractible using the
    following function:»

  commentCode canEta

  p"contribution continued"
   «All the while, neither do we require a name supply, nor is there
    a risk for name capture. Testing terms for α-equivalence remains
    straightforward and representable terms are exactly those intended.
    The cost of this achievement is the use of somewhat more involved
    types for binders, and the use of extensions of the {_Haskell}
    type-system. The new construction is informally described and
    motivated in sec. {ref overview}. In sections {ref contextSec} to
    {ref scopesSec} we present in detail the implementation of the
    technique as well as basic applications. Larger applications such as
    normalization (using hereditary substitutions), closure conversion
    and CPS transformation are presented in sec. {ref examples}.»
