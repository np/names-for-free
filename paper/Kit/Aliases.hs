{-# LANGUAGE QuasiQuotes, OverloadedStrings,
               FlexibleInstances, TemplateHaskell,
               NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Kit.Aliases where

import Language.LaTeX hiding ((<>))
import Kit.Basics
import Kit.QQ
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Math as M
import Language.LaTeX.Builder.QQ (tex)

_NaPa = B.textsc «NaPa»
_Nameless_Painless = B.textbf«Na»⊕«meless »⊕B.textbf«Pa»⊕«inless»
nompa = B.textsc «NomPa»
_NomPa = nompa
_Agda = B.textsc «Agda»
_Epigram = B.textsc «Epigram»
_Idris = B.textsc «Idris»
_Alea = B.textsc «Alea»
_DemTech = B.textsc «DemTech»
_Helios = B.textsc «Helios»
_Coq = B.textsc «Coq»
_OCaml = B.textsc «OCaml»
_Cαml = «Cαml»
_MetaML = B.textsc «MetaML»
tickC = B.textsc «`C»
_Haskell = B.textsc «Haskell»
_ML = B.textsc «ML»
_LamCirc = «λ{B.math (M.sub (M.mathCmd "bigcirc"))}»
--_LamCirc = «λ{B.math (M.sub (M.mathCmd "Ellipse"))}»
_Lisp = B.textsc «Lisp»
_FreshOCaml = B.textsc «Fresh OCaml»
_FreshML = B.textsc «FreshML»
_FreshML_Lite = B.textsc «FreshML-Lite»
_FreshLib = B.textsc «FreshLib»
_BindersUnbound = B.textsc «Binders Unbound»
_Bound = B.textsc «Bound»
_Belugaμ = «Beluga{B.math (M.sup M.mu)}»
_Template_Agda = B.textsc «Template Agda»
-- TODO => nicer
_PTS = B.textsc «PTS» -- ma[M.mathcal $ mc[M._P, M._T, M._S]]
_PoplMark = B.textsc «PoplMark»
nomSysT = «Nominal System »⊕B.math M._T
sysF = «System »⊕B.math M._F
etc = [tex|etc.\ |]
bare = B.texttt «bare»
th n = n`sup`«th»
nth = th (B.math M.n)
