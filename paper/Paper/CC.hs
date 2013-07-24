{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.CC where

import Kit
import Paper.Keys

ccDoc onlyInCode = do
  subsection $ «Closure Conversion» `labeled` closureSec
  q«A common phase in the compilation of functional languages is closure conversion. 
    The goal of closure conversion is make explicit the creation and opening of closures, 
    essentially implementing lexical scope. 
    What follows is a definition of closure conversion, as can be found in a textbook 
    (in fact this version is slightly adapted from {citet[guillemettetypepreserving2007]}).
    In it, we use a hat to distinguish
    object-level abstractions ({tm|\hat\lambda|}) from host-level ones.
    Similarly, the {tm|@|} sign is used for object-level applications. »
  q«
    The characteristic that interests us in this definition is that it is written in nominal style.
    For instance, it pretends that by matching on a {tm|\hat \lambda|}-abstraction, one obtains a name
    {tm|x|} and an expression {tm|e|}, and it is silent about the issues of freshness and
    transport of names between contexts. In the rest of the section, we construct an
    implementation which essentially retains
    these characteristics.
  »
  dmath
   [texm|
   |\begin{array}{r@{\,}l}
   |  \llbracket x \rrbracket &= x \\
   |  \llbracket \hat\lambda x. e \rrbracket &= \mathsf{closure}~(\hat\lambda x~x_\mathnormal{env}. e_\mathnormal{body})\, e_\mathnormal{env} \\
   |                                         &\quad \quad \mathsf{where}~\begin{array}[t]{l@{\,}l}
   |                                                                  y_1,\ldots,y_n & = FV(e)-\{x\} \\
   |                                                                  e_\mathnormal{body} & = \llbracket e \rrbracket[x_{env}.i/y_i] \\
   |                                                                  e_\mathnormal{env} & = \langle y_1,\ldots,y_n \rangle
   |                                                               \end{array}\\
   |  \llbracket e_1@e_2 \rrbracket &= \mathsf{let}~(x_f,x_\mathnormal{env}) = \mathsf{open}~\llbracket e_1 \rrbracket \, \mathsf{in}~ x_f \langle \llbracket e_2 \rrbracket , x_\mathnormal{env} \rangle
   |\end{array}
   |]

  q«The first step in implementing the above function is to define the
    target language. It features variables and applications as usual.
    Most importantly, it has a constructor for {|Closure|}s, composed
    of a body and an environment. The body of closures have exactly two
    free variables: {|vx|} for the parameter of the closure and {|venv|}
    for its environment.
    These variables are represented
    by two {|UnivScope|}s, which we splice in the type of the constructor.
    An environment is realized by a {|Tuple|}.
    Inside the closure, elements of the environment are accessed via
    their {|Index|} in the tuple. Finally, the {|LetOpen|} construction
    allows to access the components of a closure (its first argument)
    in an arbitrary expression (its second argument). This arbitrary
    expression has two extra free variables: {|vf|} for the code of the
    closure and {|venv|} for its environment.
     »

  -- NP: we should either change to SuccScope or mention that we illustrate
  -- here the UnivScope representation.
  -- JP: done at end of sec. 5.4
   

  [haskellFP|
  |data LC a where
  |  VarLC :: a → LC a
  |  AppLC :: LC a → LC a → LC a
  |  Closure :: (∀ vx venv. vx → venv →
  |           LC (Zero ▹ venv ▹ vx)) →
  |           LC a → LC a
  |  Tuple :: [LC a] → LC a
  |  Index :: LC a → Int → LC a
  |  LetOpen :: LC a → (∀ vf venv. vf → venv →
  |                     LC (a ▹ vf ▹ venv)) → LC a
  |]

  q«This representation is an instance of {|Functor|} and {|Monad|}, and
    the corresponding code offers no surprise.

    We give an infix alias for {|AppLC|}, named {|$$|}.»

  onlyInCode [haskellFP|
  |($$) = AppLC
  |infixl $$
  |]

  {-
  [haskellFP|
  |closure :: (∀ vx venv. vx → venv →
  |              LC (Zero ▹ venv ▹ vx)) →
  |           LC a →
  |           LC a
  |closure f t = Closure (f () ()) t
  |
  |letOpen :: LC a →
  |           (∀ vf venv. vf → venv →
  |               LC (a ▹ vf ▹ venv)) → LC a
  |letOpen t f = LetOpen t (f () ())
  |]
  -}

  q«Closure conversion can then be implemented as a function
    from {|Tm a|} to {|LC a|}. The case of variables is trivial. For
    an abstraction, one must construct a closure, whose environment
    contains each of the free variables in the body. The application
    must open the closure, explicitly applying the argument and the
    environment.»

  q«The implementation closely follows the mathematical definition
    given above. The work to manage variables explicitly is limited
    to the lifting of the substitution {tm|[x_{env}.i/y_i]|}, and an
    application of {|wk|}. Additionally, the substitution performed
    by {|wk|} is inferred automatically by GHC.»

  [haskellFP|
  |cc :: Eq a ⇒ Tm a → LC a
  |cc (Var x) = VarLC x
  |cc t0@(Lam b) =
  |  let yn = nub $ freeVars t0
  |  in Closure (λ x env → cc (b `atVar` x) >>=
  |                   liftSubst x (idxFrom yn env))
  |             (Tuple $ map VarLC yn)
  |cc (App e1 e2) =
  |  LetOpen (cc e1)
  |          (λ f x → var f $$ wk (cc e2) $$ var x)
  |]

{-
  Not really relevant since we're not tightly related to Guillemettetypepreserving2007.

  q«The definition of closure conversion we use has a single difference
    compared to {cite[guillemettetypepreserving2007]}: in closure
    creation, instead of binding one by one the free variables {|yn|} in
    the body to elements of the environment, we bind them all at once,
    using a substitution which maps variables to their position in the
    list {|yn|}.»
-}

  q«A notable difference between the above implementation and that of
    {citeauthor[guillemettetypepreserving2007]} is the following.
    They first modify the
    function to take an additional substitution argument, citing the
    difficulty to support a direct implementation with de Bruijn
    indices. We need not do any such modification: our interface is
    natural enough to support a direct implementation of the algorithm.»

ccAppendix = do
  [haskellP|
  |idxFrom :: Eq a ⇒ [a] → v → a → LC (Zero ▹ v)
  |idxFrom yn env z = Index (var env) $
  |                   fromJust (elemIndex z yn)
  |
  |instance Functor LC where
  |  fmap f t = t >>= return . f
  |
  |instance Monad LC where
  |  return = VarLC
  |  VarLC x >>= θ = θ x
  |  Closure c env >>= θ = Closure c (env >>= θ)
  |  LetOpen t g >>= θ = LetOpen (t >>= θ) 
  |    (λ f env → g f env >>= 
  |        liftSubst env (liftSubst f θ))
  |  Tuple ts >>= θ = Tuple (map (>>= θ) ts)
  |  Index t i >>= θ = Index (t >>= θ) i
  |  AppLC t u >>= θ = AppLC (t >>= θ) (u >>= θ)
  |]

  section $ «Bind and substitute an arbitrary name»
  [haskellP|
  |packGen _ t x = fmap (shuffle cx) t
  |  where cx :: v → w
  |        cx _ = x
  |
  |class (v ∈ b) ⇒ Insert v a b where
  |  -- inserting 'v' in 'a' yields 'b'.
  |  shuffle :: (v → w) → b → a ▹ w
  |
  |instance Insert v a (a ▹ v) where
  |  shuffle f (New x) = New (f x)
  |  shuffle f (Old x) = Old x
  |
  |instance Insert v a b ⇒ 
  |         Insert v (a ▹ v') (b ▹ v') where
  |  shuffle f (New x) = Old (New x)
  |  shuffle f (Old x) = case shuffle f x of
  |    New y → New y
  |    Old y → Old (Old y)
  |
  |substituteGen :: 
  |   (Insert v a b, Functor tm, Monad tm) ⇒ 
  |   v → tm a → tm b → tm a
  |substituteGen x t u = 
  |   substituteOut x t (fmap (shuffle id) u)
  |]
