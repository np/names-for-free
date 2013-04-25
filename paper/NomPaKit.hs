{-# LANGUAGE QuasiQuotes, FlexibleContexts, TypeSynonymInstances,
    FlexibleInstances #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-orphans #-}
module NomPaKit
  ( module NomPaKit
  , module Control.Monad.Writer
  ) where

import Control.Monad.Writer hiding (lift)
import Control.Applicative hiding ((<$>))
import Data.Foldable (Foldable,foldMap)
import qualified Data.Tree as T
-- import HSH
import qualified Text.PrettyPrint.Leijen as P
import Text.PrettyPrint.Leijen ((<+>), (<$>), Pretty(..))

import Language.LaTeX hiding ((<>))
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Builder.Color as C
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Builder.QQ (tex)

import qualified MiniTikz.Diagram as D
import MiniTikz.Builder hiding (node)
import NomPaKit.Basics
import NomPaKit.Config
import NomPaKit.DSL
import NomPaKit.QQ (frTop, frAntiq, frQQ, agdaPCode, agdaFPCode, nopagebreak)
import NomPaKit.Verb (alignVert, purple, firebrick, mediumBlue, myHstring, myCharToMath, colorizeAgdaP, verb{-, colorize-})

-- import HSH

-- qm is not exported on purpose, use m instead

ifm :: Monoid m => Bool -> m -> m
ifm True  x = x
ifm False _ = ø

-- shortcuts
diagram = put . parMarkDiag . B.center . D.diagram [nodeDistance "2cm"{-(L.cm 2)-}] -- , levelDistance (L.cm 2)]
tree :: [ScopeOpt] -> T.Tree LatexItem -> ParItemW
tree opts = put . parMarkDiag . B.center
          . D.diagram opts . (:[]) . helper where
  helper (T.Node root children) = dnode' "" [] (schild root) ((fmap . fmap) schild children)

textcolor | colorful config = C.textcolor
          | otherwise       = const id

stringTree, stringTreeFP :: [ScopeOpt] -> T.Tree String -> ParItemW
stringTree opts = tree opts  . fmap (textcolor purple . alignVert . verb False False)
numTree :: (Show a, Num a) => [ScopeOpt] -> T.Tree a -> ParItemW
numTree opts = tree opts . fmap (textcolor purple . alignVert . verb False False . show)
stringTreeFP opts t = do
  nopagebreak
  stringTree opts t
agdaProgFP n = agdaFPCode . colorizePrettyAgdaP n
agdaProgP n = agdaPCode . colorizePrettyAgdaP n
colorizePrettyAgdaP n = fromRight . colorizeAgdaP . renderDoc n . prettyP
quote = put . B.quote
textit = B.textit
emph = B.emph
emix x = B.emph x ⊕ index x
center x = B.center !$? x
cite = BI.latexCmdAnyArgs "cite" . pure . BI.latexKeysArg
shortcite = BI.latexCmdAnyArgs "shortcite" . pure . BI.mandatoryList . BI.latexKeys
dedicace = BI.latexCmdArg "dedicace"
citeComment comment key = B.comment comment ⊕ cite[key]
ref = B.ref
pageRef = («page » ⊕) . B.pageref
infix 8 `labeled`
labeled x lbl = x ⊕ B.label lbl
th n = n`sup`«th»
nth = th (B.math M.n)
blueℛτ = textcolor mediumBlue . B.math $ (myCharToMath 'ℛ') ⊕ M.sub (myCharToMath 'τ')
_TeX = B._TeX
-- math s = B.math (M.mathCmd s)

numL :: Integer -> LatexItem
numL = myHstring . show
{-
instance SymLit LatexItm where
  num = myHstring . show

instance SymLit a => SymLit (LatexM a) where
  num = return . num
-}

renderDoc n = ($"\n") . P.displayS . P.renderPretty 1 n
showTree n = renderDoc n . pretty

sumF :: (Num a, Foldable f) => f a -> a
sumF = getSum . foldMap Sum

countNodes :: (a -> Bool) -> T.Tree a -> Integer
countNodes pr = getSum . foldMap (\x -> ifm (pr x) $ Sum 1)

instance Pretty a => Pretty (T.Tree a) where
  pretty (T.Node ℓ []) =
    txt "node" <+> pretty ℓ <+> txt "[]"
  pretty (T.Node ℓ children) =
    P.group . P.hang 2 $ txt "node" <+> pretty ℓ <$> prettyAgdaList (map pretty children)

class PrettyAgda a where
  prettyAgda :: a -> P.Doc

instance PrettyAgda String where
  prettyAgda = txt . prettyShowString

instance PrettyAgda ℕ where
  prettyAgda = pretty

agdaTreeProgBase :: PrettyAgda a => Int -> T.Tree a -> String
agdaTreeProgBase n = showTree n . fmap prettyAgda

agdaTreeProg :: PrettyAgda a => Int -> T.Tree a -> ParItemW
agdaTreeProg n = agdaPCode . fromRight . colorizeAgdaP . agdaTreeProgBase n

agdaTreeProgF :: PrettyAgda a => Int -> T.Tree a -> ParItemW
agdaTreeProgF n = agdaFPCode . fromRight . colorizeAgdaP . agdaTreeProgBase n

ppw1, ppw2, ppw3, ppw4 :: Int
ppw1 = 40
ppw2 = 60
ppw3 = 70
ppw4 = 80

todo :: a -> a
todo = id
{-# DEPRECATED todo "You have something to do here" #-}

red = textcolor C.red
commentColor = textcolor firebrick
idColor = textcolor mediumBlue

_HRule  = B.rule L.linewidth (L.mm 0.5)
scLarge = B.textsc . B.decl B._Large
scLARGE = B.textsc . B.decl B._LARGE
bfLarge = B.textbf . B.decl B._Large
bfLARGE = B.textbf . B.decl B._LARGE
bf      = B.textbf
br      = B.linebr ø . Just . L.cm

paraDraft x = ifm (displayNotes config) (B.para x)

vcenter x = B.vfill ⊕ x ⊕ B.vfill

url = BI.latexCmdArg "url" . BI.rawTex
index = BI.latexCmdArg "index"
idx l x = index (mc[l,«!»,x])
indexcode = idx «Code»
ix x = x ⊕ indexcode x
ik x = x ⊕ idx «Keyword» x

-- Monadic style

p :: String -> LatexItem -> ParItemW
p nam = put . namedPara nam
chapter = put . B.chapter
section = put . B.section
subsection = put . B.subsection
subsubsection = put . B.subsubsection
_Foreword :: LatexItem -> ParItemW
_Foreword x = do put $ B.subsection' (★) ø «Foreword»
                 put $ B.para (mconcat (replicate 5 B.nbsp) `mappend` B.minipage B.normal (L.linewidth * (7/8)) (B.para x))
figure s caption key b =
  parMarkParaName "figure" .
  B.figure s ø !$
         (B.flushleft (execWriter b)
         ⊕ (B.para . B.caption $ caption `labeled` key))
newpage = put B.newpage
paragraph = put . B.paragraph' (★) Nothing
hyphen = B.hyphen
vfill = put B.vfill
note _ = mempty

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
_Belugaμ = «Beluga{B.math (M.sup M.mu)}»
_Template_Agda = B.textsc «Template Agda»
-- TODO => nicer
_PTS = B.textsc «PTS» -- ma[M.mathcal $ mc[M._P, M._T, M._S]]
_PoplMark = B.textsc «PoplMark»
nomSysT = «Nominal System »⊕B.math M._T
sysF = «System »⊕B.math M._F
etc = [tex|etc.\ |]
bare = B.texttt «bare»
