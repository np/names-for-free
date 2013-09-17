{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Snippets where

import Kit

unpackCode =  [haskellFP|
  |unpack :: f (Succ a) → 
  |          (∀ v. v → f (a ▹ v) → r) → r
  |unpack e k = k () e
  |]

apTm =
  [haskellFP|
  |-- Building the following term: λ f x → f x
  |apTm = lam $ λ f → lam $ λ x → var f `App` var x
  |]

canEta =
  [haskellFP|
  |canEta (Lam e) = unpack e $ λ x t → case t of
  |  App e1 (Var y) → y `isOccurrenceOf` x &&
  |                    x `freshFor` e1
  |  _ → False
  |canEta _ = False
  |]

-- NP: Trying to factor canEta and canEtaWithSig result
-- in big space between the signature and the code.
-- This is due to the fact haskellP/haskellFP are building
-- paragraphs.
canEtaWithSig =
  [haskellFP|
  |canEta :: Tm Zero → Bool
  |canEta (Lam e) = unpack e $ λ x t → case t of
  |  App e1 (Var y) → y `isOccurrenceOf` x &&
  |                    x `freshFor` e1
  |  _ → False
  |canEta _ = False
  |]
