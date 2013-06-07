{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures #-}
module AgdaKit.QQ where

import Control.Monad
import Language.Haskell.TH (Q, Exp)
import Language.Haskell.TH.Syntax (Lift(lift))

import Language.LaTeX.Builder.QQ (mkQQ, mkQQgen, stripIndentQQ)

import Kit.Basics
import Kit.QQ
import AgdaKit.Verb (colorizeAgdaP, agdaCodeI, agdaCodeIU, agdaCodeP)

agdaCodeQ :: Bool -> Bool -> String -> Q Exp
agdaCodeQ indented nl
    = join
    . fmap (either (fail . show) lift . colorizeAgdaP)
    . if indented
      then fmap (dropWhile (=='\n') . nlf) . stripIndentQQ
      else return
  where nlf = if nl then (++"\n") else id

-- unbreakable & aligned agda code
agdaFPCode x = nopagebreak >> agdaCodeP True True x

agdaPCode = agdaCodeP False False

agda   = mkQQgen (agdaCodeQ False False) "agda" 'agdaCodeI
-- 'U' as in Unaligned
agdaU  = mkQQgen (agdaCodeQ False False) "agdaU" 'agdaCodeIU
rawAgda= mkQQ "rawAgda" 'λCode
agdaFP = mkQQgen (agdaCodeQ True True)  "agdaFP" 'agdaFPCode
agdaP  = mkQQgen (agdaCodeQ True True)  "agdaP"  'agdaPCode
agdaQ  = mkQQgen (agdaCodeQ True False) "agdaQ"  'agdaPCode
