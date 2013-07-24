{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.NbE where

import Kit
import Paper.Keys

docNbE = do
  subsection $ «Normalisation by Evaluation» `labeled` nbeSec

  p"intro"
   «Another algorithm to normalize terms and also another classical
    test of scope respresentations is how they support normalisation by
    evaluation (NbE) {cite nbecites}.»

  q«NbE takes terms to their normal form by taking advantage of
    evaluation done by the host language.»

  p"TmS"
   «Terms are first evaluated into semantic terms where name-abstraction
    is shaped as a function from term to term, ready to substitute and
    continue normalizing with the received argument. More precisely,
    since terms are indexed by their context this “substitution as a
    function” should be ready to work in any extension of the current
    context. This forms of abstraction has been studied before in
    the context of NbE {cite nbecites}. Our implementation of NbE
    for Nested Abstract Syntax closely follows the implementation
    in {_NomPa} {cite [pouillardunified2012]}. By lack of space we only
    highlight part of the definitions and leave the details to the
    development online {cite[namesforfreerepo]}.»

{-
  [haskellFP|
  |data TmS a where
  |  LamS :: (∀ b. (a → b) → TmS b → TmS b) → TmS a
  |  VarS :: a → [TmS a] → TmS a
  |
  |evalS :: (a → TmS b) → Tm a → TmS b
  |evalS f (Var x)   = f x
  |evalS f (Lam b)   = unpack b $ λ x t →
  |                    LamS $ λ g u →
  |                      evalS (extend (x, u) (fmap g . f)) t
  |evalS f (App t u) = appS (evalS f t) (evalS f u)
  |]
  |instance Functor TmS where
  |  fmap f (LamS g)    = LamS $ λ h x → g (h . f) x
  |  fmap f (VarS x ts) = VarS (f x) (map (fmap f) ts)
  |
  |varS :: a → TmS a
  |varS x = VarS x []
  |
  |appS :: TmS a → TmS a → TmS a
  |appS (LamS f)    u = f id u
  |appS (VarS x ts) u = VarS x (ts++[u])
  |
  |extend :: (v, r) → (a → r) → (a ▹ v) → r
  |extend (_, r) _ (New _) = r
  |extend (_, _) f (Old x) = f x
  |
  |reify :: TmS a → No a
  |reify (VarS x ts) = Neutr x (map reify ts)
  |reify (LamS f)    = lamNo $ λ x →
  |                      reify (f Old (varS (New x)))
  |
  |nbe :: Tm a → No a
  |nbe = reify . evalS varS
  |]

  [haskellP|
  |data TmM a where
  |  LamM :: (∀ b. (a → TmM b) → TmM b → TmM b) → TmM a
  |  VarM :: a → [TmM a] → TmM a
  |
  |-- Unlike TmS, TmM supports a simple monad instance
  |instance Monad TmM where
  |  return x = VarM x []
  |  LamM f    >>= θ = LamM $ f . (<=< θ)
  |  VarM x ts >>= θ = foldl appM (θ x)((>>= θ)<$>ts)
  |
  |instance Functor TmM where
  |  fmap f (LamM g)    = LamM $ \ h x → g (h . f) x
  |  fmap f (VarM x ts) = VarM (f x) (map (fmap f) ts)
  |
  |appM :: TmM a → TmM a → TmM a
  |appM (LamM f)    u = f return u
  |appM (VarM x ts) u = VarM x (ts++[u])
  |
  |evalM :: (a → TmM b) → Tm a → TmM b
  |evalM f (Var x)   = f x
  |evalM f (Lam b)   = unpack b $ \ x t →
  |                    LamM $ \ g u →
  |                     evalM (extend (x, u) (g <=< f)) t
  |evalM f (App t u) = appM (evalM f t) (evalM f u)
  |
  |type ScopeM f a = ∀ b. (a → f b) → f b → f b
  |unpackM :: ScopeM TmM a → (∀ v. v → TmM (a ▹ v) → r) → r
  |unpackM s k = k () (s `atVarM` ())
  |
  |-- same as mesToUniv
  |atVarM :: ScopeM TmM a → v → TmM (a ▹ v)
  |s `atVarM` x = s (return . Old) (return (New x))
  |
  |reifyM :: TmM a → No a
  |reifyM (VarM x ts) = Neutr x (map reifyM ts)
  |reifyM (LamM s)    = unpackM s $ \ x t →
  |                       LamNo x (reifyM t)
  |
  |nbeM :: Tm a → No a
  |nbeM = reifyM . evalM return
  |]
  -}
