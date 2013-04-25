{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures #-}
module NomPaKit.QQ where

import Control.Monad
import Language.Haskell.TH.Quote
import Language.Haskell.TH (Q, Exp, appE, varE, listE, tupE)
import Language.Haskell.TH.Syntax (Lift(lift))

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder.QQ as QQ
import Language.LaTeX.Builder.QQ (mkQQ, mkQQnoIndent, mkQQgen, stripIndentQQ)

import NomPaKit.Basics
import NomPaKit.Verb (verb, verbatim, myHstring, colorizeAgdaP, mathW, agdaCodeI, agdaCodeIU, agdaCodeP)

-- λ-calculus (also used for rawAgda)
λCode = verb False True

-- Program output
output = B.dquote . verb False True

-- Quasi Quotation

keys, frQQ :: QuasiQuoter
keys = QQ.keys
frAntiq = QQ.frAntiq
frTop = QQ.frTop

agdaCodeQ :: Bool -> Bool -> String -> Q Exp
agdaCodeQ indented nl
    = join
    . fmap (either (fail . show) lift . colorizeAgdaP)
    . if indented
      then fmap (dropWhile (=='\n') . nlf) . stripIndentQQ
      else return
  where nlf = if nl then (++"\n") else id

pagebreak = put . B.parDecl . B.pagebreak
nopagebreak = put . B.para $ B.decl (B.nopagebreak Nothing) ø
rawTexP = put . B.para . BI.rawTex

-- unbreakable & aligned agda code
agdaFPCode x = nopagebreak >> agdaCodeP True True x

agdaPCode = agdaCodeP False False

doVerbatimP    = verbatim False False
doVerbatimFP x = nopagebreak >> verbatim True True x

constReturn :: Monad m => a -> m ()
constReturn _ = return ()

verbQ :: Bool -> Bool -> String -> Q Exp
verbQ mayAlign wordBreakable input
  = varE 'verb `appE` lift mayAlign `appE` lift wordBreakable `appE` lift input

nodesQparser :: String -> Q Exp
nodesQparser = ((listE . map (\line -> quadr line . breakableWords $ line)
                       . filter (not . null)
                       . map (dropWhile (==' '))
                       . lines) =<<) . stripIndentQQ
  where
    quadr _ [x,y,z,t] = tupE . map (verbQ True False) $ [x, y, z, t]
    quadr s _ = fail ("quadr on line: " ++ show s)

mathRawMath :: String -> LatexItem
mathRawMath = B.math . BI.rawMath

frQQ   = mkQQnoIndent "frQQ" 'myHstring
lc     = mkQQnoIndent "lc"   'λCode
agda   = mkQQgen (agdaCodeQ False False) "agda" 'agdaCodeI
-- 'U' as in Unaligned
agdaU  = mkQQgen (agdaCodeQ False False) "agdaU" 'agdaCodeIU
rawAgda= mkQQ "rawAgda" 'λCode
m      = mkQQnoIndent "m"    'mathW
tm     = mkQQnoIndent "tm"   'mathRawMath
agdaFP = mkQQgen (agdaCodeQ True True)  "agdaFP" 'agdaFPCode
agdaP  = mkQQgen (agdaCodeQ True True)  "agdaP"  'agdaPCode
agdaQ  = mkQQgen (agdaCodeQ True False) "agdaQ"  'agdaPCode
texP   = mkQQ "texP" 'rawTexP
nodesQ = mkQQgen nodesQparser "nodesQ" 'id
ignoreP = mkQQ "ignoreP" 'constReturn
verbatimP = mkQQ "verbatimP" 'doVerbatimP
verbatimFP = mkQQ "verbatimFP" 'doVerbatimFP
defaultQQ = agda
