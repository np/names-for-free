{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.CPS where

import Kit
import Paper.Keys

cpsDoc = do
  subsection $ «CPS Transform» `labeled` cpsSec

  p"intro"
   «The next example is a transformation to continuation-passing
    style (CPS) based partially on work by {citet[chlipalaparametric2008]} and
    {citet[guillemettetypepreserving2008]}.

    The main objective of the transformation is to make the
    order of evaluation explicit, by {tm|\mathsf{let}|}-binding every intermediate {|Value|} in
    a specific order. To this end, we target a special representation,
    where every intermediate result is named. We allow for {|Value|}s to be
    pairs, so we can easily replace each argument with a pair of an
    argument and a continuation.»

{-
  [haskellFP|
  |data TmC a where
  |  HaltC :: a → TmC a
  |  AppC  :: a → a → TmC a
  |  LetC  :: Value a → TmC (Succ a) → TmC a
  |
  |data Value a where
  |  LamC  :: TmC (Succ a) → Value a
  |  PairC :: a → a → Value a
  |  FstC  :: a → Value a
  |  SndC  :: a → Value a
  |]
-}

  [haskellFP|
  |data TmC a where
  |  HaltC :: Value a → TmC a
  |  AppC  :: Value a → Value a → TmC a
  |  LetC  :: Value a → TmC (Succ a) → TmC a
  |
  |data Value a where
  |  LamC  :: TmC (Succ a) → Value a
  |  PairC :: Value a → Value a → Value a
  |  VarC  :: a → Value a
  |  FstC  :: a → Value a
  |  SndC  :: a → Value a
  |]

  p"smart constructors"
   «We do not use {|Value|}s directly, but instead their composition with injection.»

  {-
  [haskellFP|
  |type UnivScope f a = ∀ v. v → f (a ▹ v)
  |
  |haltC :: (v ∈ a) ⇒ v → TmC a
  |appC  :: (v ∈ a, v' ∈ a) ⇒ v → v' → TmC a
  |letC  :: Value a → UnivScope TmC a → TmC a
  |
  |lamC  :: UnivScope TmC a → Value a
  |pairC :: (v ∈ a, v' ∈ a) ⇒ v → v' → Value a
  |fstC  :: (v ∈ a) ⇒ v → Value a
  |sndC  :: (v ∈ a) ⇒ v → Value a
  |]
  -}

  [haskellFP|
  |varC :: (v ∈ a) ⇒ v → Value a
  |letC :: Value a → UnivScope TmC a → TmC a
  |lamC :: UnivScope TmC a → Value a
  |fstC :: (v ∈ a) ⇒ v → Value a
  |sndC :: (v ∈ a) ⇒ v → Value a
  |]

  -- smart constructor for
  --    λ(x1,x2)→f x1 x2
  -- internally producing
  --    λp→ let x1 = fst p in
  --        let x2 = snd p in
  --        f x1 x2

  p"Functor TmC"
   «Free variables in {|TmC|} can be renamed, thus it enjoys a
    functor structure, with a straightforward implementation found
    our online development {cite[namesforfreerepo]}. However, this
    new syntax {|TmC|} is not stable under substitution. Building a
    monadic structure would be more involved, and is directly tied to
    the transformation we perform and the operational semantics of the
    language, so we omit it.»

  p"the transformation"
   «We implement a one-pass CPS transform (administrative redexes are
    not created). This is done by passing a host-language continuation
    to the transformation. At the top-level the halting continuation
    is used. A definition of the transformation using mathematical
    notation could be written as follows.»

  dmath
   [texm|
   |\begin{array}{r@{\,}l}
   | \llbracket x \rrbracket\,\kappa &= \kappa\,x \\
   | \llbracket e_1 \,@\, e_2 \rrbracket\,\kappa &= \llbracket e_1 \rrbracket (\lambda f. \,
   |                                       \llbracket e_2 \rrbracket (\lambda x. \,
   |                                       f \, @ \, \langle x, \kappa \rangle ) ) \\
   | \llbracket \hat\lambda x. e \rrbracket \kappa &= \mathsf{let}\, f = \hat\lambda p. \begin{array}[t]{l}
   |                                       \mathsf{let}\, x_1 = \mathsf{fst}\, p \,\mathsf{in}\\
   |                                       \mathsf{let}\, x_2  = \mathsf{snd}\, p \,\mathsf{in} \\
   |                                       \llbracket e[x_1/x] \rrbracket (\lambda r.\, x_2 \, @ \, r) \end{array}  \\
   |                                      &\quad \mathsf{in} \, \kappa\,f
   |\end{array}
   |]

  p"latex vs. haskell"
   «The implementation follows the above definition, except for the
    following minor differences. For the {|Lam|} case, the only
    deviation is an occurrence of {|wk|}. In the {|App|} case, we
    have an additional reification of the host-level continuation as a
    proper {|Value|} using the {|lamC|} function.

    In the variable case, we must pass the variable {|v|} to the
    continuation. Doing so yields a value of type {|TmC (a ▹ a)|}.
    To obtain a result of the right type it suffices to remove the
    extra tagging introduced by {|a ▹ a|} everywhere in the term,
    using {|(untag <$>)|}. Besides, we use a number of instances of {|wk|}, 
    and for each of them
    GHC is able to infer the substitution to perform.»

  {-
  [haskellFP|
  |cps :: Tm a → (∀ v. v → TmC (a ▹ v)) → TmC a
  |cps (Var x)     k = fmap untag (k x)
  |cps (App e1 e2) k =
  |  cps e1 $ λ f →
  |  cps (wk e2) $ λ x →
  |  LetC (LamC (λ x → wk (k x))) $ \k' →
  |  LetC (pairC x k') $ \p →
  |  appC f p
  |cps (Lam e')    k =
  |  LetC (LamC $ \p → LetC (fstC p) $ λ x →
  |                   LetC (π2 p) $ \k' →
  |                   cps (wk (e' x)) $ \r →
  |                   appC k' r)
  |      k
  |]
  -}

  -- |cps :: Tm a → Univ TmC a → TmC a
  [haskellFP|
  |cps :: Tm a → (∀ v. v → TmC (a ▹ v)) → TmC a
  |cps (Var x)     k = untag <$> k x
  |cps (App e1 e2) k =
  |  cps e1 $ λ x1 →
  |  cps (wk e2) $ λ x2 →
  |  varC x1 `AppC` (varC x2 `PairC`
  |                  lamC (λ x → wk $ k x))
  |cps (Lam e)    k =
  |  letC
  |    (lamC $ λp →
  |       letC (fstC p) $ λ x1 →
  |       letC (sndC p) $ λ x2 →
  |       cps (wk $ e `atVar` x1) $ λr →
  |       varC x2 `AppC` varC r) k
  |]
{-
  -- This version departs from the mathematical notation and requires an explicit weakening
  [haskellFP|
  |cps :: Tm a → (∀ v. v → TmC (a ▹ v)) → TmC a
  |cps (Var x)     k = untag <$> k x
  |cps (App e1 e2) k =
  |  cps e1 $ λ x1 →
  |  cps (wk e2) $ λ x2 →
  |  AppC (varC x1)
  |       (PairC (varC x2)
  |              (lamC (λ x → wk $ k x)))
  |cps (Lam e)     k =
  |  letC (lamPairC $ λ x1 x2 →
  |        cps (fmap Old $ e `atVar` x1) $ λr →
  |        AppC (varC x2) (varC r)) k
  |
  |cps0 :: Tm a → TmC a
  |cps0 t = cps t $ HaltC . varC
  |]

  -- I suggest inlining this so meaningful names can be used.
  -- |type UnivScope2 f a = forall v1 v2. v1 → v2 → f (a ▹ v1 ▹ v2)
  [haskellFP|
  |lamPairC :: (forall v1 v2. v1 → 
  |             v2 → TmC (a ▹ v1 ▹ v2)) → Value a
  |lamPairC f = lamC $ λp →
  |              letC (fstC p) $ λ x1 →
  |              letC (sndC p) $ λ x2 →
  |              wk $ f x1 x2
  |]
-}

  q«It is folklore that a CPS transformation is easier
    to implement with higher-order abstract syntax
    {cite[guillemettetypepreserving2008,washburnboxes2003]}. Our
    interface for name abstractions features a form of higher-order
    representation. (Namely, a quantification, over a universally
    quantified type.) However limited, this higher-order aspect is
    enough to allow an easy implementation of the CPS transform.»

cpsAppendix = do
{-
  |  fmap f (FstC x)    = FstC (f x)
  |  fmap f (SndC x)    = SndC (f x)
  |  fmap f (PairC x y) = PairC (f x) (f y)
  |  fmap f (LamC t)    = LamC (fmap (mapOld f) t)

  |  fmap f (HaltC x)  = HaltC (f x)
  |  fmap f (AppC x y) = AppC (f x) (f y)
  |  fmap f (LetC p t) = LetC (fmap f p) (fmap (mapOld f) t)
  -}
  [haskellP|
  |instance Functor Value where
  |  fmap f (VarC x)      = VarC (f x)
  |  fmap f (FstC x)      = FstC (f x)
  |  fmap f (SndC x)      = SndC (f x)
  |  fmap f (PairC v1 v2) = 
  |     PairC (fmap f v1) (fmap f v2)
  |  fmap f (LamC t)      =
  |     LamC (fmap (mapOld f) t)
  |
  |instance Functor TmC where
  |  fmap f (HaltC v)    = HaltC (fmap f v)
  |  fmap f (AppC v1 v2) = 
  |     AppC  (fmap f v1) (fmap f v2)
  |  fmap f (LetC p t)   = 
  |     LetC (fmap f p) (fmap (mapOld f) t)
  |]

  [haskellP|
  |letC p f = LetC p (f ())
  |varC = VarC . inj
  |lamC f = LamC (f ())
  |fstC = FstC . inj
  |sndC = SndC . inj
  |]

{-
  |letC p f  = LetC p (f ())
  |lamC f    = LamC (f ())
  |pairC x y = PairC (inj x) (inj y)
  |fstC      = FstC . inj
  |sndC      = SndC . inj
  |appC x y  = AppC (inj x) (inj y)
  |haltC     = HaltC . inj
  -}

  [haskellP|
  |cps0 :: Tm a → TmC a
  |cps0 t = cps t $ HaltC . varC
  |]
