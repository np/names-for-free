{-# LANGUAGE QuasiQuotes, OverloadedStrings,
               FlexibleInstances, TemplateHaskell,
               NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Kit
  (module Kit
  ,module Kit.Aliases
  ,module Kit.Config
  ,module Kit.Style
  ,module Kit.QQ
  ,module Kit.ACM
  ,module Kit.Haskell.QQ
  ,module Language.LaTeX
  ,module Control.Monad.Writer
  ,system,doesFileExist,getArgs
  ) where

import Prelude hiding (words)

import Data.List hiding (words)
import Data.List.Split (splitOneOf)
import Data.Maybe (maybeToList)
import Data.String (fromString)
import Data.Generics.Uniplate.Data (universeBi)
import Data.Char

import Control.Monad.Writer
import Control.Applicative ((<$>),pure)
import System.Cmd (system)
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import qualified System.FilePath as FP

import HSH

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Types as T
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Slicer (slice)

import Kit.Char (mnsymbol)
import Kit.Preamble
import Kit.ACM
import Kit.Config
import Kit.Basics
import Kit.IEEE
import Kit.Aliases
import Kit.Style
import Kit.QQ
import Kit.Haskell.QQ

defaultQQ = haskell


infix 8 `labeled`
labeled x lbl = x ⊕ B.label lbl

ref = B.ref

begin = BI.latexCmdArg "begin"
end = BI.latexCmdArg "end"

acknowledgments x = tell $ B.para $ BI.latexCmdArg "acks" mempty <> x

p :: String -> LatexItem -> ParItemW
p nam = put . namedPara nam
q = p ""
pc = tell . B.center . B.para
pcm = tell . B.center . B.displaymath
dmath = tell . B.displaymath
itp = tell . return . B.item
it = itp . B.para
itpm = itp . B.displaymath
itm = it . B.math -- fmap (T.LatexCast . T.MathItm) . T.mathItmM
newpageIfSparse | sparseSections config = (newpage >>)
                | otherwise             = id
section    = newpageIfSparse . put . B.section
subsection = newpageIfSparse . put . B.subsection
paragraph = put . B.paragraph' (★) Nothing
itemize block = B.itemize Nothing !$? block
footnote = B.footnote
newpage = tell B.newpage

intodo
  | displayNotes config = \ x -> red «(TODO: {x})»
  | otherwise           = const ø
{-# DEPRECATED intodo "You have something to do here" #-}

notetodo
  | displayNotes config = \ x -> p"" $ red «TODO {x}»
  | otherwise           = const $ return ()
{-# DEPRECATED notetodo "You have something to do here" #-}

--notecomm x = p"" $ red «COMMENT {x}»

doComment :: ParItemW -> ParItemW
doComment x = startComment >> x >> stopComment

commentWhen :: Bool -> ParItemW -> ParItemW
commentWhen True  x = doComment x
commentWhen False x = x

commentCode = doComment

mkabstract = BI.parEnv "abstract" [] . BI.latexItem

llncs msize mpaper args =
  B.documentclass (BI.otherDocumentClassKind "llncs") $
     maybeToList (BI.latexPaper <$> mpaper) ++
     maybeToList (BI.texLength <$> msize) ++
     args


hyphs = B.hyphenation ["crypto--graphic"] -- kept as an example

data Comment = Comment String
             | Indent (Int -> Int)
             | Nop

cite = BI.latexCmdAnyArgs "cite" . pure . BI.latexKeysArg

citet :: [Key] -> LatexItem
citet = BI.latexCmdAnyArgs "citet" . pure . BI.latexKeysArg

_Citet :: [Key] -> LatexItem
_Citet = BI.latexCmdAnyArgs "Citet" . pure . BI.latexKeysArg

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

showDocumentComments = unlines . commentsOf
printComments = putStrLn . showDocumentComments
writeCommentsTo destFile = writeFile destFile . showDocumentComments

document title authors keywords abstract categ body appendix = B.document docclass preamble body'
  where
    docclass = sigplanconf (Just (L.pt 9)) Nothing
                  (fmap BI.latexItem [«authoryear»])
    preamble =
        usepackage [] "color" <>
        fonts <>
        B.title title <>
        [qp|
        |\special{papersize=8.5in,11in}
        |\setlength{\pdfpageheight}{\paperheight}
        |\setlength{\pdfpagewidth}{\paperwidth}
        |] <>
        hyphs <>
        exclusivelicense <>
        conferenceinfo «Haskell '13» «September 23−24 2013, Boston, MA, USA» <>
        copyrightyear 2013 <>
        copyrightdata «978-1-4503-2383-3/13/09» <>
        doi «2503778.2503780» <>
        mconcat (map authorinfo authors)
    body' = B.maketitle
          <> mkabstract abstract 
          <> categ
          <> B.para (begin "keywords" <> keywords <> end "keywords")
          <> body
          <> B.para [tex|\bibliographystyle{abbrvnat}|]
          <> mapNonEmpty (B.bibliography . mconcat . intersperse [tex|,|])
                         [«../../local»,«../../npouillard»,«../../jp»]
          <> B.newpage
          <> mapNonEmpty (B.appendix <>) appendix

compile :: [FilePath] -> FilePath -> LatexM Document -> IO ()
compile input_dirs docName doc = do
  let fp         = docName FP.<.> "tex"
      opts       = input_dirs >>= \x -> ["-I",x
                                        ,"-c","bibtex.path "++x
                                        ,"-c","bibtex.stylepath "++x
                                        ,"-c","index.path "++x
                                        ,"-c","makeidx.path "++x
                                        ]
      builddir   = "_build" FP.</> docName
      runIOS x y = runIO (x::String,y::[String]) :: IO ()
  writeFile fp =<< either error return (showLaTeX doc)
  runIOS "mkdir"    ["-p",builddir]
  runIOS "rubber" $ ["--verbose","--cache","--into",builddir,"--pdf"]++opts++[fp]
