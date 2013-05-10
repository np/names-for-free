{-# LANGUAGE QuasiQuotes, OverloadedStrings,
               FlexibleInstances, TemplateHaskell,
               NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Kit where

import Prelude hiding (words)

import Data.List hiding (words)
import Data.List.Split (splitOneOf)
import Data.Maybe (maybeToList)
import Data.String (fromString)
import Data.Generics.Uniplate.Data (universeBi)
import Language.LaTeX

import Control.Applicative ((<$>),pure)

import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Types as T
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Builder.QQ
import Language.LaTeX.Slicer (slice)

import NomPaKit.Char (mnsymbol)

authorinfo (name, email', inst') =
  BI.preambleCmdArgs "authorinfo" $ map (BI.mandatory . BI.latexItem) [name, inst', email']

begin = BI.latexCmdArg "begin"
end = BI.latexCmdArg "end"

p = tell . B.para
pc = tell . B.center . B.para
pcm = tell . B.center . B.displaymath
dmath = tell . B.displaymath
itp = tell . return . B.item
it = itp . B.para
itpm = itp . B.displaymath
itm = it . B.math -- fmap (T.LatexCast . T.MathItm) . T.mathItmM
section titl lbl = tell . B.section $ titl <> B.label lbl
itemize block = B.itemize Nothing !$? block
footnote = B.footnote

mkabstract = BI.parEnv "abstract" [] . BI.latexItem

llncs msize mpaper args =
  B.documentclass (BI.otherDocumentClassKind "llncs") $
     maybeToList (BI.latexPaper <$> mpaper) ++
     maybeToList (BI.texLength <$> msize) ++
     args

ieee msize mpaper args =
  B.documentclass (BI.otherDocumentClassKind "IEEEtran") $
     maybeToList (BI.latexPaper <$> mpaper) ++
     maybeToList (BI.texLength <$> msize) ++
     args

sigplanconf msize mpaper args =
  B.documentclass (BI.otherDocumentClassKind "sigplanconf") $
     maybeToList (BI.latexPaper <$> mpaper) ++
     maybeToList (BI.texLength <$> msize) ++
     args


inst = BI.latexCmdArg "inst"
email = BI.latexCmdArg "email"

usepackage :: [String] -> String -> PreambleItem
usepackage xs = BI.usepackage (map BI.rawAnyTex xs) . BI.pkgName

hyphs = B.hyphenation ["crypto--graphic"]

data Comment = Comment String
             | Indent (Int -> Int)
             | Nop

citet :: [Key] -> LatexItem
citet = BI.latexCmdAnyArgs "citet" . pure . BI.latexKeysArg

citeauthor :: [Key] -> LatexItem
citeauthor = BI.latexCmdAnyArgs "citeauthor" . pure . BI.latexKeysArg


viewNote (T.LatexNote (T.MkKey "comment") (T.TextNote x) y) | y == ø = Comment x
viewNote (T.LatexNote (T.MkKey "indent") _ _) = Indent (+1)
viewNote (T.LatexNote (T.MkKey "dedent") _ _) = Indent (subtract 1)
viewNote _ = Nop

commentsOf = processIndentation 0 . map viewNote . universeBi

processIndentation _ []               = []
processIndentation i (Nop       : xs) = processIndentation i xs
processIndentation i (Indent  f : xs) = processIndentation (f i) xs
processIndentation i (Comment x : xs) = pI x ++ "" : processIndentation i xs
  where pI = map indentLine . lines
        indentLine "" = ""
        indentLine ys = replicate (i*2) ' ' ++ ys

emptyTextNote = T.TextNote ø
startComment = tell . B.para $ B.comment "{- --"
stopComment  = tell . B.para $ B.comment "-- -}"
indent       = tell . B.para . return $ T.LatexNote (T.MkKey "indent") emptyTextNote ø
dedent       = tell . B.para . return $ T.LatexNote (T.MkKey "dedent") emptyTextNote ø

writeAgdaTo destFile doc = writeFile destFile . unlines $ commentsOf doc

document title authors keywords abstract body appendix = B.document docclass preamble body'
  where
    docclass = sigplanconf (Just (L.pt 9)) Nothing
                  (fmap BI.latexItem [«preprint»,«authoryear»])
    -- sep = BI.rawTex " \\\\ "
    andS = BI.rawTex " \\and "
    preamble =
        usepackage [] "color" <>
        usepackage [] "tikz" <>
        fonts <>
        B.title title <>
        hyphs <>
        mconcat (map authorinfo authors) 
        {-
        B.author (mconcat . intersperse (BI.rawTex " \\and ")
                 . map (\(namn , skola , _) -> namn <> inst (fromString (show skola)))
                 $ authors) <>
        mconcat [ B.institute $  inst <> mconcat (map ((sep<>) . email) emails)
                | (inst , emails) <- zip insts [[email | (_,i,email)<-authors,i==n]|n<-[1..]]]
        -}
    body' = B.maketitle
          <> B.para (begin "keywords" <> keywords <> end "keywords")
          <> mkabstract abstract
          <> body
          <> B.para [tex|\bibliographystyle{abbrvnat}|]
          <> mapNonEmpty (B.bibliography . mconcat . intersperse [tex|,|])
                         [«../local»,«../npouillard»,«../jp»]
          <> mapNonEmpty (B.appendix <>) appendix

fonts :: PreambleItem
fonts = usepackage [] "amssymb"
      ⊕ usepackage [] "MnSymbol"
      ⊕ usepackage [] "epsdice"
      ⊕ usepackage [] "bbm"
      -- ⊕ usepackage [] "bbding"   -- to get Ellipse => BROKEN
      ⊕ usepackage [] "dsfont"   -- to get mathds => not enough symbols
      -- ⊕ usepackage [] "stmaryrd" -- To get {ll,rr}bracket
      -- ⊕ usepackage ["T3","OT1"] "fontenc"

      ⊕ [qp|\def\mynegthinspace{\!}
           |\DeclareRobustCommand{\dedicace}[1]{%
           |  \cleardoublepage
           |  \thispagestyle{empty}
           |  \vspace*{\stretch{1}}\par
           |  {\begin{flushright}\emph{#1}\end{flushright}\par}
           |  \vspace*{\stretch{2}}
           |}
           |]

      -- These two declarations are from the tipa package.
      -- However importing the packages breaks the document.
      -- Note that we require T3 fonts here. (we prefix our version with 'np')
      ⊕ [qp|\DeclareTextSymbol\nptextcrlambda{T3}{172}
           |\DeclareTextSymbolDefault\nptextcrlambda{T3}
           |]
      -- (like with tipa above)
      -- Take just a symbol from mathabx (prefixed with 'np')
      -- /usr/share/texmf-dist/tex/generic/mathabx/mathabx.dcl
      ⊕ [qp|\DeclareFontFamily{U}{npmathb}{\hyphenchar\font45}
           |\DeclareFontShape{U}{npmathb}{m}{n}{
           |      <5> <6> <7> <8> <9> <10> gen * mathb
           |      <10.95> mathb10 <12> <14.4> <17.28> <20.74> <24.88> mathb12
           |      }{}
           |\DeclareSymbolFont{npmathb}{U}{npmathb}{m}{n}
           |\DeclareFontSubstitution{U}{npmathb}{m}{n}
           |\DeclareMathSymbol{\npbigstar}   {2}{npmathb}{"0E} % to fool the highlighter => "
           |\DeclareMathSymbol{\npdotdiv}    {2}{npmathb}{"01} % to fool the highlighter => "
           |
           |\DeclareFontFamily{U}{matha}{\hyphenchar\font45}
           |\DeclareFontShape{U}{matha}{m}{n}{
           |      <5> <6> <7> <8> <9> <10> gen * matha
           |      <10.95> matha10 <12> <14.4> <17.28> <20.74> <24.88> matha12
           |      }{}
           |\DeclareSymbolFont{matha}{U}{matha}{m}{n}
           |\DeclareFontSubstitution{U}{matha}{m}{n}
           |\DeclareMathSymbol{\npoasterisk} {2}{matha}{"66} % to fool the highlighter => "
           |\DeclareMathSymbol{\npnotequiv}  {3}{matha}{"19} % to fool the highlighter => "
           |]
           {-
           -}

{-
myStrut = B.vphantom (BI.rawTex "$\\{$")

-- this should be fixed probably, I have no idea what it is doing
-- myNewline = myStrut <> B.decl (B.nopagebreak 4) (BI.latexParMode (B.newline ø))

width0_5 = "ᵣ₁₂ᴺᵂˢ"
width1 = "∀αβ·ƛ_⟦⟧⟨⟩↑øℓ∈"
width2 = "¬ℕ⟶⊎∨∧⊆"

align k = B.makebox (L.ex (k * 1.22)) B.centered

-- let's customize the rendering of some charcters in `verb' mode
-- this one doesn't work and I don't know why
{-
myXchar _ _     '\n' = myNewline
myXchar mayAlign xchar x
  | x `elem` width0_5= mayAlign (0.5 :: Rational) $ xchar x
  | x `elem` width1  = mayAlign 1 $ xchar x
  | x `elem` width2  = mayAlign 2 $ xchar x
  | x `elem` "‽"     = mayAlign 0.5 " "
  | x `elem` "="     = B.ttchar x
  | x `elem` "{}"    = M.mchar B.hchar x
  | x `elem` "("     = mayAlign 1 . B.math $ M.lparen -- mleft '('
  | x `elem` ")"     = mayAlign 1 . B.math $ M.rparen -- mright ')'
myXchar _ xchar x      = xchar x
-}

-- verb mayAlign = B.texttt . B.spaceProtector (myXchar mayAlign (M.mchar B.ttchar))

-- do not cut on unbreakable spaces
-- words = filter (not.null) . splitOneOf " \t\n"

-- word breakable code
-- wCode = B.unwords . map (verb (const id)) . words

{-
pCode x = tell . {-(B.comment x <>) .-} B.para . ([tex|~\\~|] <>)
              . verb align . dropWhile (=='\n') $ x


-- agdaCode  = wCode
agdaPCode = pCode

agda  = mkQQ "agda"  'agdaCode
agdaP = mkQQ "agdaP" 'agdaPCode
-}
-}
