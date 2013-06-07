{-# LANGUAGE QuasiQuotes #-}
module Kit.Char (myHchar, myMchar, subscriptChars, superscriptChars, mnsymbol) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.String
import Control.Arrow (second)
import Control.Applicative

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder.Math as M
import Language.LaTeX.Builder.QQ (texm, tex)

import Kit.Config

-- Math commands

defeq :: MathItem
defeq = M.stackrel (M.mathtt (M.decl M.scriptscriptstyle [texm|def|])) [texm|=|]
circarrow :: MathItem
circarrow = M.stackrel M.circ M.rightarrow
stmaryrd, amssymb, mnsymbol, epsdice :: PackageName
stmaryrd = BI.pkgName "stmaryrd"
amssymb = BI.pkgName "amssymb"
mnsymbol = BI.pkgName "MnSymbol"
epsdice = BI.pkgName "epsdice"

-- improve and move to hlatex
texErr :: String -> LatexItem
texErr | typesetErrors config = ([tex|ERROR |] <>) . fromString
       | otherwise            = error . ("texErr:" <>)

mathCmdArgIn :: PackageName -> String -> MathItem -> MathItem
mathCmdArgIn pkg name arg = M.mathCmdArgs name [BI.packageDependency pkg, BI.mandatory (BI.mathItem arg)]

mathCmdIn :: PackageName -> String -> MathItem
mathCmdIn pkg name = M.mathCmdArgs name [BI.packageDependency pkg]

ensuremath :: MathItem -> LatexItem
ensuremath = BI.latexCmdAnyArg "ensuremath" . BI.mathItem

dice :: Int -> MathItem
dice x
  | x >= 1 && x <= 6 = M.mathCmdArgs "epsdice"
                                     [ BI.packageDependency epsdice
                                     , BI.mandatory . BI.mathItem . fromIntegral $ x ]
  | otherwise = error $ "dice: out of range " ++ show x

-- Symbols

zipscripts :: (Char -> a) -> String -> String -> [(Char, a)]
zipscripts f ascii unicode = zip unicode (map f ascii)

subscripts, superscripts :: [(Char,LatexItem)]
subscriptAscii, subscriptChars, superscriptAscii, superscriptChars :: String

-- Check Yi/Char/Unicode before improving this list
subscripts   = zipscripts (B.math.M.sub.fromString.pure) subscriptAscii subscriptChars

subscriptAscii = "0123456789+-=()aeioruvx"++"hklmnpst"
subscriptChars = "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑᵢₒᵣᵤᵥₓ"++ hklmnpst
 where hklmnpst = "\8341\8342\8343\8344\8345\8346\8347\8348"
 -- "ₕₖₗₘₙₚₛₜ" http://hackage.haskell.org/trac/ghc/ticket/5519

-- Check Yi/Char/Unicode before improving this list
superscripts = zipscripts (B.textsuperscript.fromString.pure) -- NOTE that qCFQSVXYZ are missing
                 superscriptAscii superscriptChars

superscriptAscii = "0123456789+-=()abcdefghijklmnoprstuvwxyzABDEGHIJKLMNOPRTUW"
superscriptChars = "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾᴿᵀᵁᵂ"

asciibase :: [(Char, LatexItem)]
asciibase = f <$> concat [['a'..'z'],['A'..'Z'],['0'..'9']," \n:!@#$%^&*(){}[]\",.;<>/?=+-_\\|~"]
  where f x = (x, B.hchar x)

textsymbols :: [(Char, LatexItem)]
textsymbols =
  [ c '∷' $ fromString "::"
  , c 'ƛ' $ BI.texCmdNoArg "nptextcrlambda"
  , c ' ' $ B.nbsp
  , c '“' $ B.ldq
  , c '”' $ B.rdq
  , c '`' $ [tex|{`}|]
  , c '\'' $ [tex|{'}|]

  , c 'ⁿ' (myHchar '\8345' {- 'ₙ' -}) -- TODO ugly hack to workaround GHC #5519
  , c '™' $ myHchar 'ᵀ' ⊕ myHchar 'ᵐ'

  , a 'à' B.grave 'a'
  , a 'è' B.grave 'e'
  , a 'ù' B.grave 'u'
  , a 'Û' B.grave 'U'
  , a 'À' B.grave 'A'
  , a 'é' B.acute 'e'
  , a 'É' B.acute 'E'
  , a 'â' B.circ  'a'
  , a 'ê' B.circ  'e'
  , a 'î' B.circ  'i'
  , a 'ô' B.circ  'o'
  , a 'û' B.circ  'u'
  , a 'ä' B.uml   'a'
  , a 'ë' B.uml   'e'
  , a 'ï' B.uml   'i'
  , a 'ö' B.uml   'o'
  , a 'ü' B.uml   'u'
  , a 'ç' B.cedil 'c'
  ]
  where c x val = (x, val)
        a x f y = (x, f (B.hchar y))

-- This alias is a workaround to comply with idiotic rules
-- of the \index command which interpret “!” specially.
negthinspace :: MathItem
negthinspace = M.mathCmd "mynegthinspace"

mathsymbols :: [(Char, MathItem)]
mathsymbols =
  [ c '∎' $ M.decl M.scriptstyle (mathCmdIn amssymb "blacksquare")
  , c '∶' $ [texm|:|] -- TODO find better
  , c '∨' $ M.vee
  , c '⟦' $ mathCmdIn stmaryrd "llbracket"
  , c '⟧' $ mathCmdIn stmaryrd "rrbracket"
  , c '⟨' $ M.langle
  , c '⟩' $ M.rangle
  , c '⟪' $ M.langle ⊕ negthinspace ⊕ M.langle -- lAngle
  , c '⟫' $ M.rangle ⊕ negthinspace ⊕ M.rangle -- rAngle
  , c 'ᵣ' $ M.sub M.r -- this could go with subscripts but here the use of math font is nice
  , c '↦' $ M.mathCmd "mapsto"
  , c '↣' $ M.mathCmd "rightarrowtail"
  , c '⇴' $ circarrow
  , c '↪' $ M.mathCmd "hookrightarrow"
  , c '↝' $ M.mathCmd "leadsto"
  , c '⇓' $ M.mathCmd "Downarrow"
  , c '≝' $ defeq
  , c '★' $ M.mathCmd "npbigstar"
  , c '◅' $ M.mathCmd "triangleleft"
  , c '⊛' $ M.mathCmd "npoasterisk"
  , c 'ℓ' $ M.mathCmd "ell"
  , c '≗' $ mathCmdIn amssymb "circeq"
  , c '⊎' $ mathCmdIn amssymb "uplus"
  , c '′' $ M.sup (M.mathCmd "prime")
  , c '∸' $ M.mathCmd "npdotdiv"
  , c '≢' $ M.mathCmd "npnotequiv"
  , c '𝔼' $ M.mathbb M._E
  , c '≔' $ fromString ":" ⊕ negthinspace ⊕ fromString "=" -- or \coloneqq or \mathrel{\mathop:}=
  , c '≅' $ M.mathCmd "cong"
  , c '≇' $ M.mathCmd "ncong"
  , c '∼' $ M.mathCmd "sim"
  , c '≈' $ M.mathCmd "approx"
  -- , c '≋' $ mathCmdIn mnsymbol "triplesim"
  , c '≋' $ [texm|TODOTRIPPLESIM|]
  , c '⊔' $ M.mathCmd "sqcup"
  , c '⊓' $ M.mathCmd "sqcap"
  , c '⅁' $ M.mathcal M._G
  , c '⊞' $ M.mathCmd "boxplus"
  , c '⊠' $ M.mathCmd "boxtimes"
  , c '⚀' $ dice 1
  , c '⚁' $ dice 2
  , c '⚂' $ dice 3
  , c '⚃' $ dice 4
  , c '⚄' $ dice 5
  , c '⚅' $ dice 6
  , c '∙' $ M.mathCmd "bullet"
  , c '✓' $ M.mathCmd "checkmark"
  , c '‼' $ M.negthinspace
  , c '∇' $ M.nabla
  , c '𝟘' $ ds M._O
  , c '𝟙' $ bb 1
  , c '𝟚' $ bb 2
  ]
  where c x val = (x, val)
        bb x = mathCmdArgIn (BI.pkgName "bbm") "mathbbm" x
        ds x = mathCmdArgIn (BI.pkgName "dsfont") "mathds" x

unicodesymbols :: [(Char, LatexItem)]
unicodesymbols = superscripts
               ⊕ subscripts
               ⊕ (map . second) ensuremath mathsymbols -- ensuremath could be replaced by B.math
               ⊕ textsymbols
               ⊕ asciibase

unicodesymbolsMap :: Map Char LatexItem
unicodesymbolsMap = Map.fromList unicodesymbols

myMchar :: (Char -> LatexItem) -> Char -> LatexItem
myMchar mchar x =
   fromMaybe (mchar x) (Map.lookup x unicodesymbolsMap)

myHchar :: Char -> LatexItem
myHchar = myMchar (M.mchar (texErr . ("myHchar: " ++) . pure))
