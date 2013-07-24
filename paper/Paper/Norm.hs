{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Norm where

import Kit
import Paper.Keys

normDoc = do
  subsection $ «Normalization using hereditary substitution» `labeled` hereditarySec
  q«A standard test of binder representations is how well they support normalization. 
    In this section we show how to implement normalization using our constructions.»
  -- Normalization takes terms to their normal forms. 
  q«The following type
    captures normal forms of the untyped λ-calculus: a normal form is
    either an abstraction over a normal form or a neutral term (a variable applied to some normal forms). In
    this definition we use an existential-based version of scopes, which
    we splice in the {|LamNo|} constructor.»

  [haskellFP|
  |data No a where
  |  LamNo :: v → No (a ▹ v) → No a
  |  Neutr :: a → [No a] → No a
  |]

  q«The key to this normalization procedure is that normal forms
    are stable under hereditary substitution {cite hereditarycites}.
    The function performing a hereditary substitution substitutes
    variables for their value, while reducing redexes on the fly.»

  [haskellFP|
  |instance Monad No where
  |  return x = Neutr x []
  |  LamNo x t  >>= θ = LamNo x (t >>= liftSubst x θ)
  |  Neutr f ts >>= θ = foldl app (θ f)((>>= θ)<$>ts)
  |]

  q«The most notable feature of this substitution is the use of {|app|}
    to normalize redexes:»

  [haskellFP|
  |app :: No a → No a → No a
  |app (LamNo x t)  u = substituteOut x u t
  |app (Neutr f ts) u = Neutr f (ts++[u])
  |]

  q«The normalize is then a simple recursion on the term
    structure:»

  [haskellFP|
  |norm :: Tm a → No a
  |norm (Var x)   = return x
  |norm (App t u) = app (norm t) (norm u)
  |norm (Lam b)   = unpack b $ λ x t →
  |                   LamNo x (norm t)
  |]

normAppendix =
  [haskellP|
  |instance Functor No where 
  |  fmap f (LamNo x t)  = 
  |     LamNo x (fmap (mapOld f) t)
  |  fmap f (Neutr x ts) =
  |     Neutr (f x) (fmap (fmap f) ts)
  |
  |lamNo :: (∀ v. v → No (a ▹ v)) → No a
  |lamNo f = LamNo () (f ())
  |]
