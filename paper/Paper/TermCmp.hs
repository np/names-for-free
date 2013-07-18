{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.TermCmp where

import Kit
import Paper.Keys

termCmpDoc = do
  subsection $ «Test of α-equivalence»
  p""
   «Using our technique, two α-equivalent terms will have the same
    underlying representation. Despite this property, a {_Haskell}
    compiler will refuse to generate an equality-test via a {|deriving
    Eq|} clause. This is caused by the presence of a function type
    inside the {|Tm|} type. Indeed, in general, extensional equality of
    functions is undecidable. Fortunately, equality for the parametric
    function type that we use {emph«is»} decidable. Indeed, thanks to
    parametricity, the functions cannot inspect their argument at all,
    and therefore it is sufficient to test for equality at the unit
    type, as shown below:»

  commentCode [haskellFP|
  |instance Eq a ⇒ Eq (Tm a) where
  |  Var x == Var x' = x == x'
  |  Lam g == Lam g' = g == g'
  |  App t u == App t' u' = t == t' && u == u'
  |]
  -- NP: I would like to see my more general cmpTm

  q«However the application of {|()|} is somewhat worrisome, because now
    different indices might get the same {|()|} type. Even though the
    possibility of a mistake is very low in code as simple as equality,
    one might want to do more complex analyses where the possibility of
    a mistake is real. In order to preempt errors, one should like to
    use the {|unpack|} combinator as below:»

  commentCode [haskellFP|
  |  Lam g == Lam g' = unpack g  $ λx  t  →
  |                    unpack g' $ λx' t' →
  |                    t == t'
  |]

  q«This is however incorrect. Indeed, the fresh variables {|x|} and
    {|x'|} would receive incompatible types, and in turn {|t|} and
    {|t'|} would not have the same type and cannot be compared. Hence
    we must use another variant of the {|unpack|} combinator, which
    maintains the correspondence between contexts in two different
    terms.»

  [haskellFP|
  |unpack2 :: (∀ v. v → f (a ▹ v)) →
  |           (∀ v. v → g (a ▹ v)) →
  |
  |           (∀ v. v → f (a ▹ v) →
  |                       g (a ▹ v) → b) →
  |           b
  |unpack2 f f' k = k fresh (f fresh) (f' fresh)
  |  where fresh = ()
  |]

  q«One can see {|unpack2|} as allocating a single fresh name {|x|} which is shared between {|t|} and {|t'|}.»

  commentCode [haskellFP|
  |  Lam g == Lam g' = unpack2 g g' $ λ x t t' →
  |                    t == t'
  |]

  [haskellFP|
  |type Cmp a b = a → b → Bool
  |
  |cmpTm :: Cmp a b → Cmp (Tm a) (Tm b)
  |cmpTm cmp (Var x1)    (Var x2)    =
  |  cmp x1 x2
  |cmpTm cmp (App t1 u1) (App t2 u2) =
  |  cmpTm cmp t1 t2 && cmpTm cmp u1 u2
  |cmpTm cmp (Lam f1) (Lam f2) =
  |  unpack f1 $ λ x1 t1 →
  |  unpack f2 $ λ x2 t2 →
  |  cmpTm (extendCmp x1 x2 cmp) t1 t2
  |cmpTm _ _ _ = False
  |
  |-- The two first arguments are ignored and thus only there
  |-- to help the user not make a mistake about a' and b'.
  |extendCmp :: a' → b' → Cmp a b → Cmp (a ▹ a') (b ▹ b')
  |extendCmp _ _ f (Old x) (Old y) = f x y
  |extendCmp _ _ _ (New _) (New _) = True
  |extendCmp _ _ _ _       _       = False
  |]
