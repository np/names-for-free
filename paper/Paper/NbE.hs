{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.NbE where

import Language.LaTeX

import System.Cmd (system)
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import Control.Monad.Writer

import Language.LaTeX.Builder.QQ (texm, texFile)

import Kit
import Kit.Aliases
import Kit.Style
import Kit.QQ
import Kit.ACM
import AgdaKit.QQ

docNbE label nbecites = do
  subsection $ «Normalisation by Evaluation» `labeled` label

  p"intro"
   «A classical test of scope respresentations is how they support
    normalisation by evaluation (NbE) {cite nbecites}.»

  q«NbE takes terms to their normal form by taking advantage of
    evaluation done by the host language. The following type captures
    normal forms of the untyped λ-calculus: a normal form is either an
    abstraction or a variable applied to some normal forms. In this
    definition we use an existential-based version of scopes, which we
    splice in the {|LamNo|} constructor.»

  [agdaP|
  |lamNo :: (∀ v. v → No (a ▹ v)) → No a
  |lamNo f = LamNo () (f ())
  |]


  p"Sem"
   «Terms are first evaluated into semantic terms where name-abstraction TODO»

  [agdaFP|
  |data Sem a where
  |  LamS :: (∀ b. (a → b) → Sem b → Sem b) → Sem a
  |  VarS :: a → [Sem a] → Sem a
  |
  |instance Functor Sem where
  |  fmap f (LamS g)    = LamS $ λ h x → g (h . f) x
  |  fmap f (VarS x ts) = VarS (f x) (map (fmap f) ts)
  |
  |varS :: a → Sem a
  |varS x = VarS x []
  |
  |eval :: (a → Sem b) → Tm a → Sem b
  |eval f (Var x)   = f x
  |eval f (Lam b)   = unpack b $ λ x t →
  |                   LamS $ λ g u →
  |                     eval (extend (x, u) (fmap g . f)) t
  |eval f (App t u) = appS (eval f t) (eval f u)
  |
  |appS :: Sem a → Sem a → Sem a
  |appS (LamS f)    u = f id u
  |appS (VarS x ts) u = VarS x (ts++[u])
  |
  |extend :: (v, r) → (a → r) → (a ▹ v) → r
  |extend (_, r) _ (New _) = r
  |extend (_, _) f (Old x) = f x
  |
  |reify :: Sem a → No a
  |reify (VarS x ts) = Neutr x (map reify ts)
  |reify (LamS f)    = lamNo $ λ x →
  |                      reify (f Old (varS (New x)))
  |
  |nbe :: Tm a → No a
  |nbe = reify . eval varS
  |]

  [agdaP|
  |data TmM a where
  |  LamM :: (∀ b. (a → TmM b) → TmM b → TmM b) → TmM a
  |  VarM :: a → [TmM a] → TmM a
  |
  |instance Functor TmM where
  |  fmap f (LamM g)    = LamM $ \ h x → g (h . f) x
  |  fmap f (VarM x ts) = VarM (f x) (map (fmap f) ts)
  |
  |-- Unlike Sem, TmM supports a simple 
  |instance Monad TmM where
  |  return x = VarM x []
  |  LamM f    >>= θ = LamM $ f . (<=< θ)
  |  VarM x ts >>= θ = foldl appM (θ x)((>>= θ)<$>ts)
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
