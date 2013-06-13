{-# LANGUAGE TemplateHaskell #-}
module Kit.Haskell.QQ where

import Language.Haskell.TH.Quote (QuasiQuoter)

import Language.LaTeX
import Language.LaTeX.Builder.QQ (mkQQgen)

import Kit.Basics
import Kit.QQ (reifyQ)
import Kit.Haskell.Verb (haskellCode, haskellCodeP)

haskellFPCode, haskellPCode :: String -> ParItemW
haskellCodeU {-,haskellCodeI-} :: String -> LatexItem
haskell, haskellFP, haskellP :: QuasiQuoter

{-
  unbreakable inline code:
    nbsp are turned into normal spaces
 -}
haskellCodeU = haskellCode False True False True

{-
  breakable inline code
    (it seems that the support for nbsp is broken so we temporarily
     no longer use it)
haskellCodeI    = haskellCode True True False False
-}

-- unbreakable & aligned agda code
haskellFPCode x = nopagebreak >> haskellCodeP True True x
haskellPCode    = haskellCodeP False False

haskell   = mkQQgen (reifyQ False) "haskell"   'haskellCodeU
haskellFP = mkQQgen (reifyQ True)  "haskellFP" 'haskellFPCode
haskellP  = mkQQgen (reifyQ True)  "haskellP"  'haskellPCode
