{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim
module Paper.Cata where

import Kit
import Paper.Keys

cataDoc = do
  subsection «Catamorphisms in style»
  q «One can take the example of a size function, counting the number of
    data constructors in a term:»

  [haskellFP|
  |type Size = Int
  |]

  [haskellFP|
  |size :: (a → Size) → Tm a → Size
  |size ρ (Var x)   = ρ x
  |size ρ (App t u) = 1 + size ρ t + size ρ u
  |size ρ (Lam b)   = 1 + size ρ' b
  | where ρ' (New ()) = 1
  |       ρ' (Old  x) = ρ x
  |]

  p"Nominal aspect"
   «However one might prefer to use our interface in particular in larger examples.
    Each binder is simply {|unpack|}ed.
    Using this technique, the size computation looks as follows:»

  [haskellFP|
  |sizeEx :: (a → Size) → Tm a → Size
  |sizeEx ρ (Var x)   = ρ x
  |sizeEx ρ (App t u) = 1 + sizeEx ρ t + sizeEx ρ u
  |sizeEx ρ (Lam b)   = unpack b $ λ x t →
  |                      1 + sizeEx (extend (x,1) ρ) t
  |]

  p"cata"
   «This pattern can be generalized to any algebra over terms, yielding
    the following catamorphism over terms. Note that the algebra
    corresponds to the higher-order representation of λ-terms.»

  [haskellFP|
  |data TmAlg a r = TmAlg { pVar :: a → r
  |                       , pLam :: (r → r) → r
  |                       , pApp :: r → r → r }
  |
  |cata :: TmAlg a r → Tm a → r
  |cata φ s = case s of
  |   Var x   → pVar φ x
  |   Lam b   → pLam φ (λ x → cata (extendAlg x φ) b)
  |   App t u → pApp φ (cata φ t) (cata φ u)
  |
  |extendAlg :: r → TmAlg a r → TmAlg (Succ a) r
  |extendAlg x φ = φ { pVar = pVarSucc }
  |  where
  |    pVarSucc (New _) = x
  |    pVarSucc (Old y) = pVar φ y
  |]

  p"cataSize"
   «Finally, it is also possible to use {|cata|} to compute the size:»

  [haskellFP|
  |sizeAlg :: (a → Size) → TmAlg a Size
  |sizeAlg ρ = TmAlg { pVar = ρ
  |                  , pLam = λ f → 1 + f 1
  |                  , pApp = λ x y → 1 + x + y }
  |
  |cataSize :: (a → Size) → Tm a → Size
  |cataSize = cata . sizeAlg
  |]

{-

  q«
   Our representation features three aspects which are usually kept separate. It
   has a nominal aspect, an higher-order aspect, and a de Bruijn indices aspect.
   Consequently, one can take advantage of the benefits of each of there aspects when
   manipulating terms.

  ...»

  ...

  p"higher-order"«Second, we show the higher-order aspect. It is common in higher-order representations
   to supply a concrete value to substitute for a variable at each binding site.
   Consequently we will assume that all free variables
   are substituted for their size, and here the function will have type {|Tm Int → Int|}.

   In our {|size|} function, we will consider that each variable occurrence as the constant
   size 1 for the purpose of this example.

   This is be realized by applying the constant 1 at every function argument of a {|Lam|} constructor. One then needs
   to adjust the type to forget the difference between the new variable and the others, by applying an {|untag|} function
   for every variable. The variable and application cases then offer no surprises.
   »

  [haskellFP|
  |size1 :: Tm Size → Size
  |size1 (Var x) = x
  |size1 (Lam g) = 1 + size1 (fmap untag (g 1))
  |size1 (App t u) = 1 + size1 t + size1 u
  |]

  -- Scope Tm a → v → Tm (a ▹ v)
  -- Scope Tm a → a → Tm a

  {- NP: not sure about the usefulness of this

  p"de Bruijn"«Third, we demonstrate the de Bruijn index aspect. This time we assume an environment mapping
      de Bruijn indices {|Nat|} to the  their value of the free variables they represent (a {|Size|}
      in our case).
      In the input term, free variables
      are represented merely by their index.
      When going under a binder represented by a function {|g|}, we apply {|g|} to a dummy argument {|()|},
      then we convert the structure of free variables {|Nat :> ()|} into {|Nat|}, using the {|toNat|} function.
      Additionally the environment is extended with the expected value for the new variable.»

  [haskellFP|
  |size3 :: (Nat → Size) → Tm Nat → Size
  |size3 f (Var x) = f x
  |size3 f (Lam g) = 1 + size3 f' (fmap toNat (g ()))
  |  where f' Zero = 1
  |        f' (Succ n) = f n
  |size3 f (App t u) = 1 + size3 f t + size f u
  |
  |toNat (New ()) = Zero
  |toNat (Old x) = Succ x
  |]

  p"mixed style"«
  In our experience it is often convenient to combine the first and third approaches, as we
  illustrate below.
  This time the environment maps an arbitrary context {|a|} to a value.
  For each new variable,
  we pass the size that we want to assign to it to the binding function, and
  we extend the environment to use that value on the new variable, or
  lookup in the old environment otherwise.
  »
  -}
  -}

