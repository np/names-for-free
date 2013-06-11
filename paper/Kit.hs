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
import Data.Char

import Control.Applicative ((<$>),pure)

import HSH

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Types as T
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Length as L
import Language.LaTeX.Builder.QQ
import Language.LaTeX.Slicer (slice)

import Kit.Char (mnsymbol)
import Kit.Preamble
import Kit.ACM
import Kit.Basics
import Kit.IEEE
import AgdaKit.QQ

defaultQQ = agda


infix 8 `labeled`
labeled x lbl = x ⊕ B.label lbl

ref = B.ref

begin = BI.latexCmdArg "begin"
end = BI.latexCmdArg "end"

acknowledgements x = tell $ B.para $ BI.latexCmdArg "acks" mempty <> x

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
section = put . B.section
subsection = put . B.subsection
paragraph = put . B.paragraph' (★) Nothing
itemize block = B.itemize Nothing !$? block
footnote = B.footnote

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

showAgdaDocument = unlines . commentsOf
printAgdaDocument = putStrLn . showAgdaDocument
writeAgdaTo destFile = writeFile destFile . showAgdaDocument

document title authors keywords abstract categ body appendix = B.document docclass preamble body'
  where
    docclass = sigplanconf (Just (L.pt 9)) Nothing
                  (fmap BI.latexItem [«preprint»,«authoryear»])
    preamble =
        usepackage [] "color" <>
        fonts <>
        B.title title <>
        hyphs <>
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
  let texFile = docName++".tex"
      saneChar x = isAscii x && (isLetter x || isNumber x || x `elem` "_-./")
      sane x | all saneChar x = x
             | otherwise      = error "insane chars"
      opts = concatMap (\x -> "-I "++sane x) input_dirs
      builddir = sane $ "_build/"++docName
  writeFile texFile =<< either error return (showLaTeX doc)
  runIO $ "mkdir -p " ++ builddir
  runIO $ "rubber --cache --into " ++ builddir ++ " --pdf " ++ opts ++ " " ++ texFile
