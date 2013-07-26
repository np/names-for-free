{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures #-}
module Kit.QQ
  (module Kit.QQ
  ,tex
  ,qp
  ,texm
  ,texFile
  ,texmFile)
  where

import Language.Haskell.TH.Quote
import Language.Haskell.TH (Q, Exp, appE, varE, listE, tupE)
import Language.Haskell.TH.Syntax (Lift(lift))

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder.QQ as QQ
import Language.LaTeX.Builder.QQ

import Kit.Basics
import Kit.Verb (verb, verbatim, myHstring, mathW)

-- maybe move it hlatex
reifyQ :: Bool -> String -> Q Exp
reifyQ indented
  | indented  = (lift . dropWhile (=='\n') =<<) . stripIndentQQ
  | otherwise = lift

-- λ-calculus (also used for rawAgda)
λCode = verb False True

-- Program output
output = B.dquote . verb False True

-- Quasi Quotation

keys, frQQ :: QuasiQuoter
keys = QQ.keys
frAntiq = QQ.frAntiq
frTop = QQ.frTop

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
m      = mkQQnoIndent "m"    'mathW
tm     = mkQQnoIndent "tm"   'mathRawMath
texP   = mkQQ "texP" 'rawTexP
nodesQ = mkQQgen nodesQparser "nodesQ" 'id
ignoreP = mkQQ "ignoreP" 'constReturn
verbatimP = mkQQ "verbatimP" 'doVerbatimP
verbatimFP = mkQQ "verbatimFP" 'doVerbatimFP
