{-# LANGUAGE TemplateHaskell #-}
module Kit.Haskell.QQ where

import Language.Haskell.TH.Quote (QuasiQuoter)

import Language.LaTeX
import Language.LaTeX.Builder.QQ (mkQQgen)

import Kit.Basics
import Kit.QQ (reifyQ)
import Kit.Haskell.Verb (haskellCode, haskellCodeP)

haskellFPCode, haskellPCode :: String -> ParItemW
haskellCodeI :: String -> LatexItem
haskell, haskellFP, haskellP :: QuasiQuoter

haskellCodeI    = haskellCode True True False
-- unbreakable & aligned agda code
haskellFPCode x = nopagebreak >> haskellCodeP True True x
haskellPCode    = haskellCodeP False False

haskell   = mkQQgen (reifyQ False) "haskell"   'haskellCodeI
haskellFP = mkQQgen (reifyQ True)  "haskellFP" 'haskellFPCode
haskellP  = mkQQgen (reifyQ True)  "haskellP"  'haskellPCode
